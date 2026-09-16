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

% There is a bug involving the interaction between ntheorem and thmtools,
% tracked at https://github.com/muzimuzhi/thmtools/issues/77
% Without the patch below, you need to redo the \theoremstyle command before
% *every* \newtheorem command.  For \newtheorem*, the result is worse, resulting
% in a hard error if \theoremstyle isn't redone.
%
% The reason is that thmtools re-issues the current theorem style after every
% \newtheorem, but passes the *unexpanded* token \thmt@outerstyle to ntheorem,
% which stores it in the \theorem@style token register.  This causes the style
% to be resolved at *use* time rather than at definition time, so every
% environment not immediately preceded by a \theoremstyle command silently ends
% up with whatever style was declared last.  Expanding the name here makes the
% style stick at definition time.
\@ifundefined{thmt@originalthmstyle}{}{%
  \let\zariski@orig@thmstyle\thmt@originalthmstyle
  \def\thmt@originalthmstyle#1{%
    \edef\zariski@tmp@style{#1}%
    \expandafter\zariski@orig@thmstyle\expandafter{\zariski@tmp@style}}%
}

% Verweise + Stichwortverzeicnis
\RequirePackage[linkcolor=black, colorlinks=true, citecolor=black,hypertexnames=false]{hyperref}
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
