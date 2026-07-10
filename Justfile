# Format and regenerate keys of references.bib
format-bib:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

# Generate the import graph of ProvabilityLogic as import_graph.{png,pdf} (requires graphviz)
import-graph:
    lake exe graph --to ProvabilityLogic import_graph.png import_graph.pdf

# Count lines of Lean source in ProvabilityLogic/, excluding blank and comment lines (requires cloc)
cloc:
    cloc --include-lang=Lean ProvabilityLogic/
