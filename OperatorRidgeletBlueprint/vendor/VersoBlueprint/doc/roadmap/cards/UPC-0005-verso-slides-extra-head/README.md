# UPC-0005 Verso Slides Extra Head

Status: resolved
Kind: upstream-api
Priority: medium
Origin: upstream-verso-slides
Last reviewed: 2026-07-16
Owner: none
Issue: none linked
PR: https://github.com/leanprover/verso-slides/pull/59
Upstream timing: none
Removal target: none; the post-RC commit pin has been removed
Related cards: UPC-0004, UPC-0006

## Summary

Verso Slides needed module-script/head injection support so Blueprint slide decks
could load normal ESM preview runtime files.

## Impact

Without Slides `extraHead`, Blueprint had to carry a de-ESMified slide runtime
path. With upstream support, slide decks can use the same ESM preview runtime
shape as normal Blueprint pages.

## Roadmap Decision

Resolved. The `verso-slides` v4.32.0 release includes `Config.extraHead`, and
Blueprint uses the normal v4.32.0 release pin.

## Reproduction Status

Covered by Blueprint slide-deck generation and browser validation.

## Preliminary Analysis

The needed API was an upstream Slides `Config.extraHead` hook. That hook lets
Blueprint inject the slide-specific ESM entrypoint without changing the Slides
writer.

## Scope Boundary

This card covered only head injection. Structured asset declaration remains
UPC-0004, while reuse of the upstream Slides traversal/render/output pipeline
remains UPC-0006.

## Expected Behavior

Blueprint slide decks write normal preview ESM support files, load a
slide-specific runtime entrypoint, pass the preview renderer explicitly to slide
hydration, and avoid a de-ESMified `blueprint-slides.js` bundle.

## Evidence

- Upstream PR: https://github.com/leanprover/verso-slides/pull/59
- Upstream status: `Config.extraHead` is in the `verso-slides` v4.32.0 tag.
- Local release pin: `lakefile.lean` requires `verso-slides` v4.32.0.

## Current Workaround

None. Blueprint loads the slide runtime through `Config.extraHead` from the
normal `verso-slides` v4.32.0 release.
