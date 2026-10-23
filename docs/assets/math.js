// Typeset mathematics on the documentation site.
// 1. TeX statements that lean-pkg writes as ```latex code blocks (docs/verification.md,
//    docs/coverage.md) are shown typeset, with the exact TeX source kept under a toggle.
//    The generated Markdown is not modified, so `lean-pkg page --check` stays valid.
// 2. Inline $...$ / \(...\) and display $$...$$ / \[...\] elsewhere on a page are typeset.
// 3. A statement that is a whole manuscript excerpt (\begin{lemma}, \begin{table}, ...) cannot be
//    typeset as a fragment; when MathJax reports an error for it, the typeset copy is removed and
//    the exact TeX source is shown unfolded instead, so a reader never sees an error box.
// MathJax never touches <pre>/<code>, so Lean code stays literal. \require and the html
// extension (\href, \class, ...) are disabled: statement text cannot add links or markup.
(function () {
  function convertTexBlocks(root) {
    var codes = (root || document).querySelectorAll("pre > code.language-latex, div.language-latex pre > code");
    codes.forEach(function (code) {
      var box = code.closest("div.language-latex") || code.closest("pre");
      if (!box || box.dataset.texDone) return;
      box.dataset.texDone = "1";
      var shown = document.createElement("div");
      shown.className = "tex-statement";
      shown.textContent = code.textContent;          // text node: no HTML is interpreted
      var details = document.createElement("details");
      details.className = "tex-source";
      var summary = document.createElement("summary");
      summary.textContent = "TeX source";
      box.parentNode.insertBefore(shown, box);
      box.parentNode.insertBefore(details, box);
      details.appendChild(summary);
      details.appendChild(box);
    });
  }
  function fallBackToSource() {
    document.querySelectorAll(".tex-statement").forEach(function (shown) {
      if (!shown.querySelector("mjx-merror")) return;
      var details = shown.nextElementSibling;
      if (details && details.classList.contains("tex-source")) details.open = true;
      shown.remove();
    });
  }
  var typesetHref = null;   // the page MathJax has already typeset
  window.texBlocks = { convert: convertTexBlocks };
  window.MathJax = {
    tex: {
      inlineMath: [["$", "$"], ["\\(", "\\)"]],
      displayMath: [["$$", "$$"], ["\\[", "\\]"]],
      processEscapes: true,
      packages: { "[-]": ["require", "autoload"] },
      macros: { label: ["", 1] }   // manuscript labels repeat across excerpts; they are not shown
    },
    options: { ignoreHtmlClass: "tex-source|tex2jax_ignore" },
    startup: {
      ready: function () {
        convertTexBlocks(document);
        MathJax.startup.defaultReady();
        MathJax.startup.promise.then(fallBackToSource);
        typesetHref = location.href;
      }
    }
  };
  // MkDocs Material instant navigation: re-run on every page change.
  if (typeof document$ !== "undefined") {
    document$.subscribe(function () {
      // The first emission is the initial page, which MathJax's startup typesets itself.
      if (!window.MathJax || !MathJax.typesetPromise || location.href === typesetHref) return;
      convertTexBlocks(document);
      MathJax.startup.output.clearCache();
      MathJax.typesetClear();
      MathJax.texReset();
      MathJax.typesetPromise().then(function () { fallBackToSource(); typesetHref = location.href; });
    });
  }
})();
