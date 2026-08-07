#!/usr/bin/env bash
#
# init-latex-project.sh
# Scaffolds a basic LaTeX project with a sensible directory structure.
#
# Usage:
#   ./init-latex-project.sh <project-name> ["Document Title"] ["Author Name"]
#
# Example:
#   ./init-latex-project.sh my-thesis "My Thesis" "Jane Doe"

set -euo pipefail

PROJECT_NAME="${1:-latex-project}"
TITLE="${2:-Document Title}"
AUTHOR="${3:-Author Name}"

if [ -e "$PROJECT_NAME" ]; then
  echo "Error: '$PROJECT_NAME' already exists." >&2
  exit 1
fi

echo "Creating LaTeX project '$PROJECT_NAME'..."

mkdir -p "$PROJECT_NAME"/{sections,figures,bib}

# --- main.tex ---------------------------------------------------------
cat > "$PROJECT_NAME/main.tex" << EOF
\documentclass[11pt,a4paper]{article}

% --- Packages ---
\usepackage[utf8]{inputenc}
\usepackage[T1]{fontenc}
\usepackage{geometry}
\geometry{margin=1in}
\usepackage{graphicx}
\usepackage{amsmath,amssymb}
\usepackage{hyperref}
\usepackage[style=numeric,sorting=none]{biblatex}
\addbibresource{bib/references.bib}

% --- Metadata ---
\title{$TITLE}
\author{$AUTHOR}
\date{\today}

\begin{document}

\maketitle
\tableofcontents
\newpage

\input{sections/introduction}
\input{sections/methods}
\input{sections/results}
\input{sections/conclusion}

\newpage
\printbibliography

\end{document}
EOF

# --- Section stubs ------------------------------------------------------
cat > "$PROJECT_NAME/sections/introduction.tex" << 'EOF'
\section{Introduction}

Write your introduction here.
EOF

cat > "$PROJECT_NAME/sections/methods.tex" << 'EOF'
\section{Methods}

Describe your methods here.
EOF

cat > "$PROJECT_NAME/sections/results.tex" << 'EOF'
\section{Results}

Present your results here.
EOF

cat > "$PROJECT_NAME/sections/conclusion.tex" << 'EOF'
\section{Conclusion}

Summarize your conclusions here.
EOF

# --- Bibliography ---------------------------------------------------------
cat > "$PROJECT_NAME/bib/references.bib" << 'EOF'
@article{example2024,
  author  = {Doe, Jane},
  title   = {An Example Article},
  journal = {Journal of Examples},
  year    = {2024},
  volume  = {1},
  pages   = {1--10}
}
EOF

# --- .gitignore ---------------------------------------------------------
cat > "$PROJECT_NAME/.gitignore" << 'EOF'
# LaTeX auxiliary files
*.aux
*.bbl
*.bcf
*.blg
*.fdb_latexmk
*.fls
*.log
*.out
*.run.xml
*.synctex.gz
*.toc
*.xdv

# Bibliography backend
*-blx.bib

# Editor / OS files
.DS_Store
*.swp
EOF

# --- Makefile ---------------------------------------------------------
cat > "$PROJECT_NAME/Makefile" << 'EOF'
MAIN = main

all: $(MAIN).pdf

$(MAIN).pdf: $(MAIN).tex
	latexmk -pdf -interaction=nonstopmode $(MAIN).tex

clean:
	latexmk -C
	rm -f sections/*.aux

.PHONY: all clean
EOF

echo "Done. Project created at ./$PROJECT_NAME"
echo
echo "Next steps:"
echo "  cd $PROJECT_NAME"
echo "  make          # builds main.pdf using latexmk"
echo "  make clean    # removes auxiliary/build files"