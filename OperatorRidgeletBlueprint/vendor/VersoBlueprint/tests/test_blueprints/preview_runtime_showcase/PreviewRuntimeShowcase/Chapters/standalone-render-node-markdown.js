(function () {
  const { loadPreviewApi, onDomReady } = createBlueprintPreviewApiLoader(window);

  function appendTextNode(parent, tagName, className, text) {
    const node = document.createElement(tagName);
    if (className) node.className = className;
    node.textContent = text;
    parent.appendChild(node);
    return node;
  }

  function appendMarkdownInline(parent, text) {
    String(text || "").split(/(\*\*[^*]+\*\*)/g).forEach(function (part) {
      if (!part) return;
      if (part.startsWith("**") && part.endsWith("**") && part.length > 4) {
        appendTextNode(parent, "strong", "", part.slice(2, -2));
      } else {
        parent.appendChild(document.createTextNode(part));
      }
    });
  }

  async function renderMarkdown(payload, target) {
    const fragment = document.createDocumentFragment();
    String(payload.raw || "").split(/\n+/).map(function (line) {
      return line.trim();
    }).filter(Boolean).forEach(function (line) {
      if (line.startsWith("# ")) {
        appendTextNode(fragment, "h4", "", line.slice(2).trim());
      } else {
        const paragraph = document.createElement("p");
        appendMarkdownInline(paragraph, line);
        fragment.appendChild(paragraph);
      }
    });
    target.replaceChildren(fragment);
  }

  async function renderStandaloneNode(api, root) {
    if (!(root instanceof HTMLElement)) return;
    if (root.dataset.bpStandaloneRenderNodeBound === "true") return;
    root.dataset.bpStandaloneRenderNodeBound = "true";
    const target = root.querySelector("[data-bp-standalone-render-node-target]");
    if (!(target instanceof Element)) return;
    const result = await api.renderNode(target, {
      label: root.dataset.bpLabel || "",
      facet: root.dataset.bpFacet || "statement",
      externalMarkup: {
        prefer: [
          { language: "markdown", slot: "original", render: renderMarkdown },
          { display: "source" }
        ]
      }
    });
    root.dataset.bpRenderOk = result.ok ? "true" : "false";
    root.dataset.bpRenderMode = result.renderMode || "";
    root.dataset.bpRenderReason = result.reason || "";
    root.dataset.bpPreviewKey = result.key || "";
    root.dataset.bpCanonicalPreview = result.canonicalHtml ? "true" : "false";
    root.dataset.bpManifestLabel =
      result.manifestEntry && result.manifestEntry.label ? result.manifestEntry.label : "";
    root.dataset.bpExternalMarkupLanguage =
      result.externalMarkup && result.externalMarkup.language ? result.externalMarkup.language : "";
  }

  function bindAll(api) {
    document.querySelectorAll("[data-bp-standalone-render-node-markdown]").forEach(function (root) {
      renderStandaloneNode(api, root);
    });
  }

  function reportLoadError(err) {
    document.querySelectorAll("[data-bp-standalone-render-node-markdown]").forEach(function (root) {
      if (!(root instanceof HTMLElement)) return;
      root.dataset.bpRenderOk = "false";
      root.dataset.bpRenderReason = err && err.message ? err.message : String(err);
    });
  }

  loadPreviewApi().then(function (api) {
    onDomReady(function () {
      bindAll(api);
    });
  }).catch(function (err) {
    onDomReady(function () {
      reportLoadError(err);
    });
  });
})();
