#!/bin/sh

if [ -z "$1" ]
then
	cat >&2 <<EOF
Syntax: $0 DIR
DIR is the base directory of your TeX installation, e.g. /usr/share/texmf.
EOF
	exit 1
fi

set -e

BASE="$1"

mkdir -p "$BASE/fonts/source/public/cmll"
cp mf/* "$BASE/fonts/source/public/cmll/"
mkdir -p "$BASE/fonts/type1/public/cmll"
cp type1/* "$BASE/fonts/type1/public/cmll/"
mkdir -p "$BASE/fonts/tfm/public/cmll"
cp tfm/* "$BASE/fonts/tfm/public/cmll/"
mkdir -p "$BASE/fonts/map/dvips/cmll"
cp cmll.map "$BASE/fonts/map/dvips/cmll/"
mkdir -p "$BASE/tex/latex/cmll"
cp latex/* "$BASE/tex/latex/cmll/"
mkdir -p "$BASE/source/latex/cmll"
cp cmll.dtx cmll.ins "$BASE/source/latex/cmll/"
mkdir -p "$BASE/doc/fonts/cmll"
cp README cmll.pdf "$BASE/doc/fonts/cmll"

echo "All files are installed. You may have to run texhash now."
