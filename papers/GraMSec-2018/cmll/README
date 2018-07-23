This directory contains the CMLL font. This font contains a handful of symbols
used in the linear logic coommunity, designed for use with standard Computer
Modern and AMS Euler fonts.

This package is dated April 20, 2010.


Installation
------------

* Using packages

CMLL is part of reasonable TeX distributions (including TeXLive and MikteX).

A Debian package is available at http://iml.univ-mrs.fr/~beffara/soft/, it can
be installed even if an older version of CMLL is installed using one of the
TeXLive packages, and it will have priority over it.

* Using the shell script (for Unix)

Say
  ./install.sh /usr/share/texmf
Replace "/usr/share/texmf" by the path of the TeX directory structure where
you want to install the files.
You may have to update TeX's databases by running "texhash" or "mktexlsr"
(this is for Kpathsea-based distributions like TeX Live) or a similar command.

* By hand

Copy the .mf files from the "mf" subdirectory somewhere in Metafont's search
path and the .sty and .fd files from the "latex" subdirectory somewhere in
LaTeX's search path.

Call TEXMF the base directory of your installation (on Unix this should be
something like /usr/share/texmf or ~/texmf for a single user installation).
Then copy the directories as follows:
    copy "mf" as TEXMF/fonts/source/public/cmll
    copy "latex" as TEXMF/tex/latex/cmll
If you want to install the fonts in Type1 format:
    copy "type1" as TEXMF/fonts/type1/public/cmll
    copy "tfm" as TEXMF/fonts/tfm/public/cmll
    copy "cmll.map" as TEXMF/fonts/map/dvips/cmll/cmll.map
You may have to update TeX's databases by running "texhash" or "mktexlsr"
(this is for Kpathsea-based distributions like teTeX) or a similar command.


Usage
-----

When the files are correctly installed, compiling the file cmll.dtx with latex
will produce a documentation for the package, including the list of defined
symbols.

To summarise, just say \usepackage{cmll} to get the extra symbols. Class
options may be used to select a particular variant of the font, see the
documentations for details.

In order to use the Type1 versions, assuming the files are installed as
described above, you need to use the provided file "cmll.map". Please refer to
the documentation of you local installation for that.


Feedback
--------

Any comments and suggestions are welcome, feel free to drop me a note at the
address below.

For those interested in legal stuff, this work is covered by the LaTeX Project
Public License (LPPL).

Enjoy !

(c) Emmanuel Beffara <manu@beffara.org>, 2003--2010
