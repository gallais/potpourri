# Super- and subscripts.
s/‿\([^\}]*\)\\textasciicircum{}\([^\}]*\)/\^\{\\AgdaFontStyle\{\\scriptscriptstyle \2\}\}\_\{\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}/g
s/\\textasciicircum{}\([^\}]*\)‿\([^\}]*\)/\^\{\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}\_\{\\AgdaFontStyle\{\\scriptscriptstyle \2\}\}/g
s/\\textasciicircum{}\([^\}]*\)/\{\^\\AgdaFontStyle\{\\scriptscriptstyle\{\}\1\}\}/g
s/{\([^{]*\)\({\^\\AgdaFontStyle{\\scriptscriptstyle{}[^\]*}\)/\{\{\1\}\2/g
s/‿\([^\}]*\)/\_\\AgdaFontStyle\{\\scriptscriptstyle \1\}/g

s/₀/\_\{\\scriptscriptstyle\{\}0\}/g

# Latex
s/^\\begin{code}/\\begin\{code\}\n\\\\/g
s/^\\end{code}/\\\\\\end\{code\}\n/g

s/\\AgdaSymbol{\\{}.*\\AgdaSymbol{\\}}[^()]*\\AgdaSymbol{→} //g
s/\\AgdaSymbol{\\{}[^()]*\\AgdaSymbol{\\}}//g
s/\\AgdaSymbol{\\{}.*\\AgdaSymbol{\\}}//g