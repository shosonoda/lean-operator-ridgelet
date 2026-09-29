function createBlueprintPreviewApiLoader(globalScope) {
  const root = globalScope || (typeof window !== "undefined" ? window : globalThis);

  function blueprintDataUrl(filename) {
    const safeFilename = String(filename || "").trim();
    if (!safeFilename) return "-verso-data/";
    try {
      const locationHref = root.location && root.location.href ? root.location.href : "";
      const url = new URL(locationHref);
      const markers = ["/html-multi/", "/html-single/"];
      for (const marker of markers) {
        const idx = url.pathname.indexOf(marker);
        if (idx >= 0) {
          const rootPath = url.pathname.slice(0, idx + marker.length);
          return rootPath + "-verso-data/" + safeFilename;
        }
      }
    } catch (_err) {}
    return "-verso-data/" + safeFilename;
  }

  async function loadPreviewApi() {
    const candidates = [
      blueprintDataUrl("api/preview.mjs"),
      "../-verso-data/api/preview.mjs",
      "-verso-data/api/preview.mjs"
    ];
    let lastError = null;
    let preview = null;
    for (const candidate of Array.from(new Set(candidates))) {
      try {
        preview = await import(candidate);
        break;
      } catch (err) {
        lastError = err;
      }
    }
    if (!preview) throw lastError || new Error("Could not import Blueprint preview API");
    return typeof preview.createPreview === "function" ? preview.createPreview() : preview;
  }

  function onDomReady(fn) {
    const documentObj = root.document;
    if (!documentObj) return;
    if (documentObj.readyState === "loading") {
      documentObj.addEventListener("DOMContentLoaded", fn, { once: true });
    } else {
      fn();
    }
  }

  return { blueprintDataUrl, loadPreviewApi, onDomReady };
}
