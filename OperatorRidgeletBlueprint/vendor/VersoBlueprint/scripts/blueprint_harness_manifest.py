from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def load_json_object(path: Path, *, context: str | None = None) -> dict[str, Any]:
    label = context or str(path)
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as err:
        raise ValueError(f"{label}: invalid JSON: {err.msg}") from err
    if not isinstance(data, dict):
        raise ValueError(f"{label}: expected JSON object")
    return data


def resolve_manifest_path(path_text: str | None, default_path: Path) -> Path:
    if path_text is None:
        return default_path

    path = Path(path_text)
    if path.is_absolute():
        return path.resolve()
    return (Path.cwd() / path).resolve()


def require_string(data: dict[str, Any], key: str, *, context: str) -> str:
    value = data.get(key)
    if not isinstance(value, str) or not value:
        raise ValueError(f"{context}: expected non-empty string field `{key}`")
    return value


def optional_string(data: dict[str, Any], key: str, *, context: str) -> str | None:
    value = data.get(key)
    if value is None:
        return None
    if not isinstance(value, str) or not value:
        raise ValueError(f"{context}: expected non-empty string field `{key}`")
    return value


def optional_bool(data: dict[str, Any], key: str, *, default: bool, context: str) -> bool:
    value = data.get(key, default)
    if not isinstance(value, bool):
        raise ValueError(f"{context}: expected boolean field `{key}`")
    return value


def string_list(
    data: dict[str, Any],
    key: str,
    *,
    context: str,
    required: bool,
    non_empty: bool,
    unique: bool = False,
) -> tuple[str, ...] | None:
    value = data.get(key)
    if value is None and not required:
        return None

    expected = "non-empty string list" if non_empty else "string list"
    if (
        not isinstance(value, list)
        or (non_empty and not value)
        or not all(isinstance(item, str) and item for item in value)
    ):
        raise ValueError(f"{context}: expected {expected} field `{key}`")

    items = tuple(value)
    if unique and len(set(items)) != len(items):
        raise ValueError(f"{context}: duplicate values in `{key}`")
    return items


def require_string_list(
    data: dict[str, Any],
    key: str,
    *,
    context: str,
    non_empty: bool = True,
    unique: bool = False,
) -> tuple[str, ...]:
    items = string_list(data, key, context=context, required=True, non_empty=non_empty, unique=unique)
    if items is None:
        raise AssertionError("required string list parser returned None")
    return items


def optional_string_list(
    data: dict[str, Any],
    key: str,
    *,
    context: str,
    non_empty: bool = False,
    unique: bool = False,
) -> tuple[str, ...] | None:
    return string_list(data, key, context=context, required=False, non_empty=non_empty, unique=unique)


def optional_command(data: dict[str, Any], key: str, *, context: str) -> tuple[str, ...] | None:
    return optional_string_list(data, key, context=context, non_empty=True)
