\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{zariski}[2022/11/01 v1.0 Synthetic-Zariski-Article]

\LoadClass[10pt, twoside]{article}

\RequirePackage[a4paper,margin=2.5cm]{geometry}

\RequirePackage{amsmath,amssymb,mathtools}

% Schönere Tabellen / Auflistungen / Theoreme
\RequirePackage{booktabs}
\RequirePackage{enumerate}
\RequirePackage{enumitem}
\RequirePackage[thmmarks]{ntheorem}
\RequirePackage{thmtools}

% Verweise + Stichwortverzeicnis
\RequirePackage[linkcolor=black, colorlinks=true, citecolor=black]{hyperref}
\RequirePackage{nameref,cleveref}

\RequirePackage{makeidx}

% 
\RequirePackage{polyglossia}
\setdefaultlanguage{english}

% Grafiken
\RequirePackage{tikz}
\usetikzlibrary{arrows, cd, babel}

% 
\setitemize{topsep=0pt,itemsep=0ex,partopsep=1ex,parsep=1ex}
\setenumerate{topsep=0pt,itemsep=1ex,partopsep=1ex,parsep=1ex}


\theorembodyfont{}
\theoremstyle{break}
    \newtheorem{theorem}{Theorem}[subsection]
    \newtheorem{lemma}[theorem]{Lemma}
    \newtheorem{definition}[theorem]{Definition}
    \newtheorem{remark}[theorem]{Remark}
    \newtheorem{example}[theorem]{Example}
    \newtheorem{corollary}[theorem]{Corollary}
    \newtheorem{proposition}[theorem]{Proposition}
    
\theoremstyle{nonumberplain}
\theoremstyle{break}
    \newtheorem*{axiom}{Axiom}

\theoremstyle{nonumberplain}
\theoremsymbol{\ensuremath{\Box}}
    \newtheorem{proof}{Proof}

\RequirePackage{zariski}
