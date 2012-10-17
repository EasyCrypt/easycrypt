#!/bin/sh

# Arguments 
case $1 in
"-help" | "--help") 
  echo "./gen-pg-keywods <path>/<lexer_file>"; exit 0
esac

# Check if the file exists
if [ ! -f $1 ]  ; then
  echo "$1: No such file or directory"; exit 1
fi

lex_file=$1

keyword_file=$2


globals=$(awk '$1 ~ /let keywords_global/  {print $0}' FS=";" RS=""  $lex_file |\
          sed -e "s/keywords_global/certicrypt-program-keywords/" |\
          sed -e "s/(\*.*\*)//" |\
          sed -e "s/,.*\]/))/" |\
          sed -e "s/,.*$//" |\
			 sed -e "s/^[\ \t]*let/(defvar/" |\
          sed -e "s/=//" |\
			 sed -e "s/\[/\'(/" )

tac=$(awk '$1 ~ /let keywords_tac/  {print $0}' FS=";" RS=""  $lex_file |\
          sed -e "s/keywords_tac/certicrypt-tactics-keywords/" |\
          sed -e "s/(\*.*\*)//" |\
          sed -e "s/,.*\]/))/" |\
          sed -e "s/,.*$//" |\
			 sed -e "s/^[\ \t]*let/(defvar/" |\
          sed -e "s/=//" |\
			 sed -e "s/\[/\'(/" )

dangerous=$(awk '$1 ~ /let keywords_dangerous/  {print $0}' FS=";" RS=""  $lex_file |\
          sed -e "s/keywords_dangerous/certicrypt-tactics2-keywords/" |\
          sed -e "s/(\*.*\*)//" |\
          sed -e "s/,.*\]/))/" |\
          sed -e "s/,.*$//" |\
			 sed -e "s/^[\ \t]*let/(defvar/" |\
          sed -e "s/=//" |\
			 sed -e "s/\[/\'(/" )

expr_prog=$(awk '$1 ~ /let keywords_expr_prog/  {print $0}' FS=";" RS=""  $lex_file |\
          sed -e "s/keywords_expr_prog/certicrypt-common-keywords/" |\
          sed -e "s/(\*.*\*)//" |\
          sed -e "s/,.*\]/))/" |\
          sed -e "s/,.*$//" |\
			 sed -e "s/^[\ \t]*let/(defvar/" |\
          sed -e "s/=//" |\
			 sed -e "s/\[/\'(/" )

# Make a backup 
# cp $keyword_file $keyword_file.bak

echo "$tac"       > $keyword_file
echo              >> $keyword_file
echo "$globals"   >> $keyword_file
echo              >> $keyword_file
echo "$expr_prog" >> $keyword_file
echo              >> $keyword_file
echo "$dangerous" >> $keyword_file
echo              >> $keyword_file
echo "(provide 'certicrypt-keywords)" >> $keyword_file
