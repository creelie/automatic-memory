#!/usr/bin/env bash
# Builds the paper and the release files:
#   dist/Sl2WeightSystemAtMinus3Over32_final2.pdf            the paper
#   dist/Sl2WeightSystemAtMinus3Over32_final2-tex.zip        LaTeX source with the figures as PNG
#   dist/Sl2WeightSystemAtMinus3Over32_final2-arxiv.tar.gz   the same source as an arXiv tarball
#   preprintSl2WeightSystemAtMinus3Over32/Sl2WeightSystemAtMinus3Over32.pdf   the paper (only file there)
#   paper/paper1/Sl2WeightSystemAtMinus3Over32_final2.pdf     the paper
#   paper/paper2/Sl2WeightSystemAtMinus3Over32_final2-tex.zip the LaTeX source zip
#   MasterSl2WeightSystemAtMinus3Over32_masterzipfinal2.zip  every tracked file with dist/
set -euo pipefail
cd "$(dirname "$0")"
for t in latexmk zip tar git; do
  command -v "$t" >/dev/null || { echo "missing tool: $t" >&2; exit 2; }
done

name=Sl2WeightSystemAtMinus3Over32
pre=preprint${name}
master=Master${name}_masterzipfinal2.zip

(cd paper && latexmk -pdf -interaction=nonstopmode -halt-on-error main.tex >/dev/null)
if grep -E "Overfull|Underfull|undefined" paper/main.log; then
  echo "paper/main.log reports bad boxes or undefined references" >&2
  exit 1
fi

rm -rf dist
mkdir -p dist "$pre"
cp paper/main.pdf "dist/${name}_final2.pdf"
cp paper/main.pdf "$pre/${name}.pdf"

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT

src="$tmp/${name}_final2-tex"
mkdir -p "$src/figures"
cp paper/main.tex paper/elsarticle.cls "$src/"
cp paper/figures/*.png "$src/figures/"
(cd "$tmp" && zip -qr -X "${name}_final2-tex.zip" "${name}_final2-tex")
mv "$tmp/${name}_final2-tex.zip" dist/
tar -czf "dist/${name}_final2-arxiv.tar.gz" -C "$src" main.tex elsarticle.cls figures
mkdir -p paper/paper1 paper/paper2
cp "dist/${name}_final2.pdf" paper/paper1/
cp "dist/${name}_final2-tex.zip" paper/paper2/

mkdir "$tmp/Master${name}"
git ls-files -z | grep -zvE "^(dist/|${pre}/|paper/paper[12]/|${master}$)" \
  | xargs -0 -I{} cp --parents {} "$tmp/Master${name}/"
mkdir -p "$tmp/Master${name}/dist" "$tmp/Master${name}/$pre" "$tmp/Master${name}/paper/paper1" "$tmp/Master${name}/paper/paper2"
cp dist/* "$tmp/Master${name}/dist/"
cp paper/paper1/* "$tmp/Master${name}/paper/paper1/"
cp paper/paper2/* "$tmp/Master${name}/paper/paper2/"
cp "$pre/${name}.pdf" "$tmp/Master${name}/$pre/"
rm -f "$master"
(cd "$tmp" && zip -qr -X "$master" "Master${name}")
mv "$tmp/$master" .
echo "built: $(ls dist | tr '\n' ' ')$master"
