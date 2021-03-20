#!/bin/ksh
sed -n '/^%%README0-BEGIN$/,/^%%README0-END$/p' notes.tex > readme0
sed -n '/^%%README1-BEGIN$/,/^%%README1-END$/p' notes.tex > readme1
sed -n '/^%%README2-BEGIN$/,/^%%README2-END$/p' notes.tex > readme2
cat readme0 readme1 readme2 \
	| sed -e '/^%%README.*$/d' -e '/^%%%%.*$/d' > ../README.md
rm -f readme0 readme1 readme2
