# Super- and subscripts.
s/\\textasciicircum\([^\}]*\)‿\([^\}]*\)/\$\^\\AgdaFontStyle\{\\scriptscriptstyle \1\}\_\\AgdaFontStyle\{\\scriptscriptstyle \2\}\$/g

s/\\textasciicircum\([^\}]*\)/\{\^\\AgdaFontStyle\{\\scriptscriptstyle \1\}\}/g

s/‿\([^\}]*\)/\_\\AgdaFontStyle\{\\scriptscriptstyle \1\}/g

# Σ[ x ∈ X ] into (x : X) ×
s/\\AgdaRecord{Σ\[} \(.*\) \\AgdaRecord{∈} \(.*\) \\AgdaRecord{]}/\\AgdaSymbol\{(\}\1 \\AgdaSymbol\{:\} \2\\AgdaSymbol\{)\} \\AgdaFunction\{×\}/g

s/Prelude\.//g

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

# Comments.
#s/AgdaComment{\-\-/AgdaComment\{\-\\!\-/g

# Other stuff.
s/⋆/\{\^*\}/g
s/ˡ/\^{\\scriptscriptstyle l}/g
s/ʳ/\^{\\scriptscriptstyle r}/g

#s/≗/\$\\overset\{\\circ\}\{≡\}\$/g
#s/▻/\$,\$/g
#s/⁅/\\{/g
#s/⁆/\\}/g
s/｛/\\{/g
s/｝/\\}/g
s/ƛ/λ/g
s/let′/let/g
s/⊤′/⊤/g

# Latex
s/^\\begin{code}/\\begin\{code\}\n\\\\/g
s/^\\end{code}/\\\\\\end\{code\}\n/g
