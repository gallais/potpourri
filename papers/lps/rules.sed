# Super- and subscripts.
s/‿\([^\}]*\)\\textasciicircum{}\([^\}]*\)/\^\{\\AgdaFontStyle\{\\scriptscriptstyle \2\}\}\_\{\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}/g
s/\\textasciicircum{}\([^\}]*\)‿\([^\}]*\)/\^\{\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}\_\{\\AgdaFontStyle\{\\scriptscriptstyle \2\}\}/g
s/\\textasciicircum{}\([^\}]*\)/\{\^\\AgdaFontStyle\{\\scriptscriptstyle\{\}\1\}\}/g
s/{\([^{]*\)\({\^\\AgdaFontStyle{\\scriptscriptstyle{}[^\]*}\)/\{\{\1\}\2/g
s/‿\([^\}]*\)/\_\\AgdaFontStyle\{\\scriptscriptstyle \1\}/g

# Useless Name disambiguation
s/Prelude\.//g
s/Vec\.//g
s/Nat\.//g
s/Pr\.//g
s/Fin\.//g

# Bind, Kleisli extension and fmap.
s/>>=/\\mathbin\{>\\!\\!>\\mkern-6.7mu=\}/g
s/>>/\\mathbin\{>\\!\\!>}/g
s/?>=/\\mathbin\{?\\!\\!>\\mkern-6.7mu=\}/g
s/=<</\\mathbin\{=\\mkern-6.7mu<\\!\\!<\}/g
s/<\\$>/\\mathop\{<\\!\\$\\!>\}/g
s/<⊛/\\mathop\{<\\!\\!⊛\}/g
s/─\*/─\\!\\!\*/g

# Append.
s/++/+\\!+/g
s/｢/\\AF\{\\lceil\{\}\}/g
s/｣/\\AF\{\\rfloor\{\}\}/g

s/｛/\\{/g
s/｝/\\}/g

# Latex
s/^\\begin{code}/\\begin\{code\}\n\\\\/g
s/^\\end{code}/\\\\\\end\{code\}\n/g
