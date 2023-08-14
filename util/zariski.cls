% \NeedsTeXFormat{LaTeX2e}
\ProvidesClass{zariski}[2022/11/01 v1.0 Synthetic-Zariski-Article]

\LoadClass[10pt, twoside]{article}

\RequirePackage[a4paper,margin=2.5cm]{geometry}

\RequirePackage{amsmath,amssymb,mathtools,amsxtra}

% Schönere Tabellen / Auflistungen / Theoreme
\RequirePackage{booktabs}
\RequirePackage{enumerate}
\RequirePackage[shortlabels]{enumitem}
\RequirePackage[thmmarks]{ntheorem}
\RequirePackage{thmtools}

% Verweise + Stichwortverzeicnis
\RequirePackage[linkcolor=black, colorlinks=true, citecolor=black]{hyperref}
\RequirePackage[hyphenbreaks]{breakurl}
\RequirePackage{nameref,cleveref}

\RequirePackage{makeidx}

%
% \RequirePackage{polyglossia}
% \setdefaultlanguage{english}

% Referenzen
\RequirePackage[backend=biber,style=alphabetic, backref, backrefstyle=none]{biblatex}
\addbibresource{../util/literature.bib}

% Grafiken
\RequirePackage{tikz}
\usetikzlibrary{arrows, cd, babel}

%
\setitemize{topsep=0pt,itemsep=0ex,partopsep=1ex,parsep=1ex}
\setenumerate{topsep=0pt,itemsep=1ex,partopsep=1ex,parsep=1ex}


\theorembodyfont{}
\theoremstyle{break}
    \newtheorem{theorem}{Theorem}[subsection]

\theoremstyle{definition}
    \newtheorem{lemma}[theorem]{Lemma}
    \newtheorem{definition}[theorem]{Definition}
    \newtheorem{conjecture}[theorem]{Conjecture}
    \newtheorem{remark}[theorem]{Remark}
    \newtheorem{example}[theorem]{Example}
    \newtheorem{corollary}[theorem]{Corollary}
    \newtheorem{proposition}[theorem]{Proposition}

\theoremstyle{nonumberplain}
\theoremstyle{break}
    \newtheorem*{axiom}{Axiom}

\newcommand{\axiomref}[1]{\nameref{#1}}

\theoremstyle{nonumberplain}
\theoremsymbol{\ensuremath{\Box}}
    \newtheorem{proof}{Proof}

\makeindex

\RequirePackage{../util/zariski}
