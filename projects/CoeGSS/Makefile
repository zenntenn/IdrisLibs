default: DSLH.docx

%.docx: %.md
	pandoc --bibliography=CoeGSS.bib -f markdown -t docx -o $@ $<
