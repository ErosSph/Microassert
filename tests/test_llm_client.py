from email.message import Message
import io
import json
import urllib.error

import pytest

from dateassertion.llm.client import DeepSeekClient, DeepSeekConfig, LLMUnavailableError


def test_deepseek_endpoint_fallback_order_from_v1():
    client = DeepSeekClient(DeepSeekConfig(base_url="https://api.deepseek.com/v1"))
    assert client._endpoint_urls() == [
        "https://api.deepseek.com/v1/chat/completions",
        "https://api.deepseek.com/chat/completions",
    ]


def test_deepseek_endpoint_fallback_order_from_root():
    client = DeepSeekClient(DeepSeekConfig(base_url="https://api.deepseek.com"))
    assert client._endpoint_urls() == [
        "https://api.deepseek.com/chat/completions",
        "https://api.deepseek.com/v1/chat/completions",
    ]


def test_qwen_preserves_base_path_and_uses_provider_specific_thinking(monkeypatch):
    client = DeepSeekClient(DeepSeekConfig(provider="qwen", model="qwen3.8-flash",
        base_url="https://dashscope.aliyuncs.com/compatible-mode/v1", api_key_env="QWEN_API_KEY"))
    requests = []
    class Opener:
        def open(self, request, timeout):
            requests.append(request)
            return io.BytesIO(json.dumps({"id": "fixture", "model": "qwen3.8-flash",
                "choices": [{"message": {"content": '{"ok":true}'}}]}).encode())
    monkeypatch.setenv("QWEN_API_KEY", "fixture-signed.key.with.dots")
    monkeypatch.setattr(client, "_opener", lambda: Opener())
    result, metadata = client.complete_json("JSON", "JSON")
    assert result == {"ok": True}
    assert client._endpoint_urls() == ["https://dashscope.aliyuncs.com/compatible-mode/v1/chat/completions"]
    assert requests[0].get_header("Authorization") == "Bearer fixture-signed.key.with.dots"
    payload = json.loads(requests[0].data)
    assert payload["enable_thinking"] is False and "thinking" not in payload
    assert metadata["provider"] == "qwen"


def test_deepseek_redirect_switches_to_alternate_official_path(monkeypatch):
    client = DeepSeekClient(DeepSeekConfig(
        base_url="https://api.deepseek.com", proxy=None,
        max_retries=1, max_tokens=16,
    ))
    calls = []

    class Opener:
        def open(self, request, timeout):
            calls.append(request.full_url)
            if len(calls) == 1:
                headers = Message()
                headers["Location"] = request.full_url
                raise urllib.error.HTTPError(
                    request.full_url, 302, "redirect", headers, io.BytesIO(b""),
                )
            return io.BytesIO(json.dumps({
                "id": "real-id", "model": "deepseek-v4-pro",
                "choices": [{"message": {"content": '{"ok": true}'}}],
            }).encode())

    monkeypatch.setenv("DEEPSEEK_API_KEY", "test-key")
    monkeypatch.setattr(client, "_opener", lambda: Opener())
    result, metadata = client.complete_json("system", "user")
    assert result == {"ok": True}
    assert calls == [
        "https://api.deepseek.com/chat/completions",
        "https://api.deepseek.com/v1/chat/completions",
    ]
    assert metadata["endpoint"].endswith("/v1/chat/completions")


@pytest.mark.parametrize("status_code", [401, 402, 403])
def test_auth_and_billing_http_errors_are_non_retryable_provider_outages(monkeypatch, status_code):
    client = DeepSeekClient(DeepSeekConfig(
        base_url="https://api.deepseek.com", proxy=None, max_retries=4,
    ))
    calls = []

    class Opener:
        def open(self, request, timeout):
            calls.append(request.full_url)
            raise urllib.error.HTTPError(
                request.full_url, status_code, "provider error", Message(),
                io.BytesIO(b'{"error":{"message":"Insufficient Balance"}}'),
            )

    monkeypatch.setenv("DEEPSEEK_API_KEY", "test-key")
    monkeypatch.setattr(client, "_opener", lambda: Opener())
    with pytest.raises(LLMUnavailableError) as raised:
        client.complete_json("system", "user")
    assert raised.value.status_code == status_code
    assert len(calls) == 1  # No retry of credentials/billing failures.


def test_transport_retry_exhaustion_is_a_fatal_provider_outage(monkeypatch):
    client = DeepSeekClient(DeepSeekConfig(
        base_url="https://api.deepseek.com", proxy=None, max_retries=1,
    ))
    calls = []

    class Opener:
        def open(self, request, timeout):
            calls.append(request.full_url)
            raise urllib.error.URLError("proxy unavailable")

    monkeypatch.setenv("DEEPSEEK_API_KEY", "test-key")
    monkeypatch.setattr(client, "_opener", lambda: Opener())
    monkeypatch.setattr("dateassertion.llm.client.time.sleep", lambda _seconds: None)
    with pytest.raises(LLMUnavailableError, match="retry budget exhausted"):
        client.complete_json("system", "user")
    assert len(calls) == 2
