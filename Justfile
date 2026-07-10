# Format and regenerate keys of references.bib
format-bib:
    bibtool -F -r .bibtoolrsc -i ./references.bib -o references.bib
    sed -i '1{/^$/d}' references.bib

# Generate the import graph of ProvabilityLogic as import_graph.{png,pdf,html} (requires graphviz)
import-graph:
    lake exe graph --to ProvabilityLogic import_graph.png import_graph.pdf import_graph.html

# Count lines of Lean source in ProvabilityLogic/, excluding blank and comment lines (requires cloc)
cloc:
    cloc --include-lang=Lean ProvabilityLogic/

# Regenerate ProvabilityLogic.lean to include all modules (run after adding/removing files)
mk-all:
    lake exe mk_all --module
