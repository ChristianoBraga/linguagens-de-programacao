#!/bin/sh
# Build both language sites and the slides and publish them to the gh-pages branch.
set -e
cd "$(dirname "$0")"

lake exe lectures-en --output _out/en
lake exe lectures-pt --output _out/pt
lake exe slides-en --output _out/slides-en
lake exe slides-pt --output _out/slides-pt

staging=$(mktemp -d)
trap 'rm -rf "$staging"' EXIT

# Short hash plus the commit timestamp in UTC, so the stamp is the same
# whether the site is built here or on the CI runner.
version="$(TZ=UTC git log -1 --format='%h · %cd' --date=format-local:'%Y-%m-%d %H:%M UTC')"

cp -r site/. "$staging"/
sed "s/__SITE_VERSION__/$version/" site/index.html > "$staging"/index.html
cp -r _out/en/html-multi "$staging"/en
cp -r _out/pt/html-multi "$staging"/pt
mkdir -p "$staging"/slides
cp _out/slides-en/*.html _out/slides-pt/*.html "$staging"/slides/
touch "$staging"/.nojekyll

cd "$staging"
git init -q -b gh-pages
git add -A
git commit -q -m "Deploy site"
git push -f https://github.com/ChristianoBraga/programming-languages.git gh-pages
echo "Deployed to https://christianobraga.github.io/programming-languages/"
