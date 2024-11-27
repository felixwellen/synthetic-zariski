% \NeedsTeXFormat{LaTeX2e}
\ProvidesClass{zariski}[2022/11/01 v1.0 Synthetic-Zariski-Article]

\LoadClass[10pt, twoside]{article}

\RequirePackage[a4paper,margin=2.5cm]{geometry}

\RequirePackage{amsmath,amssymb,mathtools,amsxtra,stmaryrd}

% Schönere Tabellen / Auflistungen / Theoreme
\RequirePackage{booktabs}
\RequirePackage{enumerate}
\RequirePackage[shortlabels]{enumitem}
\RequirePackage[amsmath, thmmarks]{ntheorem}
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
\addbibresource{literature.bib}

% Grafiken
\RequirePackage{tikz}
\usetikzlibrary{arrows, cd, babel}

%
\setitemize{topsep=0pt,itemsep=0ex,partopsep=1ex,parsep=1ex}
\setenumerate{topsep=0pt,itemsep=1ex,partopsep=1ex,parsep=1ex}
