"""Stable verification-object taxonomy shared by requirements 1--6."""

from dateassertion.ir.schema import ObjectType


OBJECT_DESCRIPTIONS = {
    ObjectType.FSM: "State or control logic with an explicit state variable and transitions.",
    ObjectType.HANDSHAKE: "Protocol or request/response behavior with progress and stability semantics.",
    ObjectType.REGISTER_UPDATE: "A state element governed by reset, enable, update, and hold behavior.",
    ObjectType.DATAPATH: "A result related to operands by an externally meaningful arithmetic/logical contract.",
    ObjectType.PIPELINE: "A registered stage boundary with transfer, stall, valid, or flush semantics.",
    ObjectType.DECODE: "Instruction or command decode from selector fields to control outputs.",
    ObjectType.REQUEST_RESPONSE: "A temporally decoupled request followed by a completion or response event.",
    ObjectType.RESOURCE: "Ownership, arbitration, accounting, or capacity of a shared resource.",
    ObjectType.EXTENSION: "A validated design-discovered object normalized into the common Contract IR.",
    ObjectType.UNKNOWN: "Insufficient evidence for a safe classification.",
}


CORE_OBJECT_TYPES = (
    ObjectType.FSM,
    ObjectType.REGISTER_UPDATE,
    ObjectType.DATAPATH,
    ObjectType.PIPELINE,
    ObjectType.DECODE,
    ObjectType.HANDSHAKE,
    ObjectType.REQUEST_RESPONSE,
    ObjectType.RESOURCE,
)
