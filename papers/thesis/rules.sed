# Super- and subscripts.
## fix to make it work with Agda 2.4.2.4
s/\\textasciicircum\([^{]\)/\\textasciicircum\{\}\1/g
## Usual rules
s/‿\([^\}]*\)\\textasciicircum{}\([^\}]*\)/\^\{\\AgdaFontStyle\{\\scriptscriptstyle \2\}\}\_\{\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}/g
s/\\textasciicircum{}\([^.\}]*\)‿\([^\}]*\)/\^\{\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}\_\{\\AgdaFontStyle\{\\scriptscriptstyle \2\}\}/g
s/\\textasciicircum{}\([^.\}]*\)/\{\^\\AgdaFontStyle\{\\scriptscriptstyle\{\}\1\}\}/g
s/{\([^{.]*\)\({\^\\AgdaFontStyle{\\scriptscriptstyle{}[^\]*}\)/\{\{\1\}\2/g
s/‿\([^\}]*\)/\_\\AgdaFontStyle\{\\scriptscriptstyle \1\}/g

s/₀/\_\{\\scriptscriptstyle\{\}0\}/g

# Operators
s/>>=/\\mathbin\{>\\!\\!>\\mkern-6.7mu=\}/g
s/>>/\\mathbin\{>\\!\\!>}/g
s/++/+\\!+/g

# Latex
s/^\\begin{code}/\\begin\{code\}\n\\\\/g
s/^\\end{code}/\\\\\\end\{code\}\n/g

# Set levels
s/ \\AgdaBound{ℓ}//g
s/ \\AgdaPrimitive{⊔} //g
s/ \?\\AgdaBound{{ℓ}{[^{]*{[^{]*{}[^}]*}}}//g
s/\\AgdaSymbol{(}\\AgdaSymbol{)}//g

# Implicit arguments
s/\\AgdaSymbol{\\{}.*\\AgdaSymbol{\\}}[^()→;]*\\AgdaSymbol{→} //g
s/\\AgdaSymbol{\\{}[^();]*\\AgdaSymbol{\\}}//g
s/\\AgdaSymbol{\\{}[^;]*\\AgdaSymbol{\\}}//g

# Fancy mathcal
s/𝓔/\\mathcal\{E\}/g
s/𝓜/\\mathcal\{M\}/g
s/𝓢/\\mathcal\{S\}/g
