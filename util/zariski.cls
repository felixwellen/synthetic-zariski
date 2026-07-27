\LoadClass{../util/zariski-base}

\theoremseparator{.}

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

\theoremstyle{break}
    \newtheorem{axiomNum}{Axiom}
    \newtheorem*{axiom}{Axiom}

\newcommand{\axiomref}[1]{\nameref{#1}}

\theoremstyle{nonumberplain}
\theoremsymbol{\ensuremath{\quad\Box}}
    \newtheorem{proof}{Proof}
% Revert, so future theorem environments don't get the \Box.
\theoremsymbol{}

\makeindex

\RequirePackage{../util/zariski}
