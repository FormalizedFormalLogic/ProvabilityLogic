# Format and regenerate keys of references.bib
format-bib:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

# Generate the import graph of SeqPL as import_graph.{png,pdf} (requires graphviz)
import-graph:
    lake exe graph --to SeqPL import_graph.png import_graph.pdf
