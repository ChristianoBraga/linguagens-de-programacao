#!/bin/sh
# Assemble the site exactly as deploy.sh does and serve it locally, so that
# cross-tree links (notes -> slides, logo) resolve the same way they do on
# the deployed site. Pass --no-build to reuse an existing _out.
set -e
cd "$(dirname "$0")"

port="${PORT:-8000}"

if [ "$1" != "--no-build" ]; then
  lake exe lectures-en --output _out/en
  lake exe lectures-pt --output _out/pt
  lake exe slides-en --output _out/slides-en
  lake exe slides-pt --output _out/slides-pt
fi

staging=$(mktemp -d)
trap 'rm -rf "$staging"' EXIT

version="$(TZ=UTC git log -1 --format='%h · %cd' --date=format-local:'%Y-%m-%d %H:%M UTC' 2>/dev/null || echo dev)"

cp -r site/. "$staging"/
sed "s/__SITE_VERSION__/$version/" site/index.html > "$staging"/index.html
cp -r _out/en/html-multi "$staging"/en
cp -r _out/pt/html-multi "$staging"/pt
mkdir -p "$staging"/slides
cp _out/slides-en/*.html _out/slides-pt/*.html "$staging"/slides/

echo "Serving assembled site at http://localhost:$port/"
echo "  English notes:    http://localhost:$port/en/"
echo "  Portuguese notes: http://localhost:$port/pt/"
echo "  Slides:           http://localhost:$port/slides/lecture-1.en.html"
echo "Press Ctrl-C to stop."
cd "$staging"
python3 -m http.server "$port"
