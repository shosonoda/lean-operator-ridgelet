from __future__ import annotations

import json
from typing import Any, Iterable


SAMPLE_PREVIOUS_RELEASE = "v4.28.0"
SAMPLE_DEFAULT_RELEASE = "v4.29.0"
SAMPLE_DEFAULT_RC_REF = "v4.29.0-rc6"
SAMPLE_NEXT_RELEASE = "v4.30.0"
SAMPLE_NEXT_RC = "4.30-rc2"
SAMPLE_NEXT_RC_REF = "v4.30.0-rc2"


def lean_toolchain(ref: str) -> str:
    return f"leanprover/lean4:{ref}"


def official_verso_require(ref: str) -> str:
    return f'require verso from git "https://github.com/leanprover/verso"@"{ref}"'


def official_blueprint_require(ref: str) -> str:
    return f'require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint"@"{ref}"'


def release_target(
    release: str,
    *,
    toolchain: str | None = None,
    verso_ref: str | None = None,
    branch: str | None = None,
    deploy_pages: bool = True,
    **extra: Any,
) -> dict[str, Any]:
    target = {
        "id": release,
        "toolchain": toolchain or release,
        "verso_ref": verso_ref or release,
        "branch": branch or release,
        "deploy_pages": deploy_pages,
    }
    target.update(extra)
    return target


def branch_policy_json(
    *,
    default_dev: str = SAMPLE_DEFAULT_RELEASE,
    required_backports: Iterable[str] = (),
    release_targets: Iterable[dict[str, Any]] | None = None,
    version: int | None = None,
) -> str:
    default_version = 2 if release_targets is not None else 1
    policy: dict[str, Any] = {
        "version": version if version is not None else default_version,
        "default_dev_branch": default_dev,
    }
    required = list(required_backports)
    if required:
        policy["required_backport_branches"] = required
    if release_targets is not None:
        policy["release_targets"] = list(release_targets)
    return json.dumps(policy, indent=2) + "\n"


def backport_line(release: str, status: str) -> str:
    return f"Backport {release}: {status}"
