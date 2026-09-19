"""OpenAI-compatible DeepSeek/Qwen transport using the Python standard library."""

from __future__ import annotations

from dataclasses import dataclass
import json
import os
import socket
import time
import urllib.error
import urllib.request
from typing import Any


class LLMError(RuntimeError):
    pass


class LLMUnavailableError(LLMError):
    """A provider/configuration failure, distinct from an invalid LLM answer.

    Callers must abort the affected experimental stage rather than classify
    this as a rejected semantic candidate.  In particular a credential or
    balance failure cannot be repaired by asking the same model again.
    """

    def __init__(self, message: str, *, status_code: int | None = None):
        super().__init__(message)
        self.status_code = status_code


@dataclass
class DeepSeekConfig:
    base_url: str = "https://api.deepseek.com/v1"
    model: str = "deepseek-v4-pro"
    api_key_env: str = "DEEPSEEK_API_KEY"
    proxy: str | None = None
    timeout_seconds: int = 120
    max_retries: int = 1
    max_tokens: int = 4096
    thinking: str = "disabled"
    provider: str = "deepseek"


class DeepSeekClient:
    def __init__(self, config: DeepSeekConfig):
        self.config = config

    def _opener(self) -> urllib.request.OpenerDirector:
        handlers: list[Any] = []
        if self.config.proxy:
            handlers.append(urllib.request.ProxyHandler({"http": self.config.proxy, "https": self.config.proxy}))
        return urllib.request.build_opener(*handlers)

    def _endpoint_urls(self) -> list[str]:
        """Return both official OpenAI-compatible paths in preferred order."""

        base = self.config.base_url.rstrip("/")
        if self.config.provider in {"qwen", "openai-compatible"}:
            return [base + "/chat/completions"]
        if base.endswith("/v1"):
            root = base[:-3].rstrip("/")
            return [base + "/chat/completions", root + "/chat/completions"]
        return [base + "/chat/completions", base + "/v1/chat/completions"]

    def complete_json(self, system_prompt: str, user_prompt: str) -> tuple[dict[str, Any], dict[str, Any]]:
        api_key = os.environ.get(self.config.api_key_env)
        if not api_key:
            raise LLMUnavailableError(
                f"missing API key environment variable: {self.config.api_key_env}"
            )
        payload = {
            "model": self.config.model,
            "messages": [
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": user_prompt},
            ],
            "temperature": 0.0,
            "response_format": {"type": "json_object"},
            "stream": False,
            "max_tokens": self.config.max_tokens,
        }
        if self.config.provider == "qwen":
            payload["enable_thinking"] = self.config.thinking == "enabled"
        elif self.config.provider == "deepseek":
            payload["thinking"] = {"type": self.config.thinking}
        encoded_payload = json.dumps(payload).encode("utf-8")
        endpoints = self._endpoint_urls()
        endpoint_index = 0
        last_error: Exception | None = None
        for attempt in range(self.config.max_retries + 1):
            endpoint = endpoints[endpoint_index]
            request = urllib.request.Request(
                endpoint,
                data=encoded_payload,
                headers={"Authorization": f"Bearer {api_key}", "Content-Type": "application/json"},
                method="POST",
            )
            try:
                with self._opener().open(request, timeout=self.config.timeout_seconds) as response:
                    raw = json.loads(response.read().decode("utf-8"))
                content = raw["choices"][0]["message"]["content"]
                parsed = json.loads(content)
                metadata = {
                    "provider": self.config.provider,
                    "requested_model": self.config.model,
                    "response_model": raw.get("model"),
                    "usage": raw.get("usage", {}),
                    "request_id": raw.get("id"),
                    "created": raw.get("created"),
                    "endpoint": endpoint,
                    "raw_content": content,
                }
                return parsed, metadata
            except (urllib.error.URLError, urllib.error.HTTPError, socket.timeout, KeyError, IndexError, json.JSONDecodeError) as exc:
                if isinstance(exc, urllib.error.HTTPError):
                    try:
                        detail = exc.read().decode("utf-8", errors="replace")[:1000]
                    except Exception:
                        detail = ""
                    location = exc.headers.get("Location", "") if exc.headers else ""
                    provider_name = "Qwen" if self.config.provider == "qwen" else "DeepSeek"
                    message = f"{provider_name} HTTP {exc.code} location={location!r}: {detail}".replace(api_key, "[REDACTED]")
                    # Authentication/authorization/billing errors are not
                    # transient transport failures.  Do not waste retry
                    # budget and, crucially, do not let higher layers turn
                    # them into a semantic candidate rejection.
                    if exc.code in {401, 402, 403}:
                        raise LLMUnavailableError(message, status_code=exc.code) from exc
                    last_error = LLMError(message)
                    if exc.code in {301, 302, 307, 308}:
                        endpoint_index = (endpoint_index + 1) % len(endpoints)
                else:
                    last_error = exc
                if attempt < self.config.max_retries:
                    time.sleep(1.5 * (attempt + 1))
        provider_name = "Qwen" if self.config.provider == "qwen" else "DeepSeek"
        raise LLMUnavailableError(
            f"{provider_name} unavailable after retry budget exhausted: {last_error}".replace(api_key, "[REDACTED]")
        ) from last_error
