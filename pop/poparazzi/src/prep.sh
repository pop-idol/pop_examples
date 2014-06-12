#!/bin/sh

#
# preparation script for POP templlate files on the POP examples site
#


# run files through formatter

perltidy poparazzi.pl
mv poparazzi.pl.tdy poparazzi.pl

perltidy Poparazzi.pm
mv Poparazzi.pm.tdy Poparazzi.pm

perltidy POP.pm
mv POP.pm.tdy POP.pm

# generate documentation html files

/usr/bin/pod2html --title "Poparazzi.pl" poparazzi.pl > ../docs/poparazzi.pl.html
/usr/bin/pod2html --title "Poparazzi.pm" Poparazzi.pm > ../docs/Poparazzi.pm.html
/usr/bin/pod2html --title "POP.pm" POP.pm > ../docs/POP.pm.html


# cleanup

rm pod2htm*.tmp

