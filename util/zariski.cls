\LoadClass{../util/zariski-base}

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

%Numbered axioms
\theoremstyle{break}
    \newtheorem{axiomNum}{Axiom}

\theoremstyle{nonumberplain}
\theoremstyle{break}
    \newtheorem*{axiom}{Axiom}

\newcommand{\axiomref}[1]{\nameref{#1}}

\theoremstyle{nonumberplain}
\theoremsymbol{\ensuremath{\Box}}
    \newtheorem{proof}{Proof}

\makeindex

\RequirePackage{../util/zariski}
