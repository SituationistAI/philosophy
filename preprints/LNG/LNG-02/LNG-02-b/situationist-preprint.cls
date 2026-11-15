\NeedsTeXFormat{LaTeX2e}
\ProvidesClass{situationist-preprint}[2026/10/06 Situationist AI preprint class]
\LoadClass[11pt,a4paper]{article}

\RequirePackage[T1]{fontenc}
\RequirePackage[utf8]{inputenc}
\RequirePackage[sc]{mathpazo}
\RequirePackage{courier}
\linespread{1.06}
\RequirePackage[margin=1in,headheight=14pt]{geometry}
\RequirePackage{microtype}
\RequirePackage{amsmath,amssymb,amsthm}
\RequirePackage{enumitem}
\RequirePackage{booktabs}
\RequirePackage{csquotes}
\RequirePackage[round,authoryear]{natbib}
\RequirePackage[dvipsnames]{xcolor}
\RequirePackage{fancyhdr}
\RequirePackage{listings}
\RequirePackage[colorlinks=true,linkcolor=MidnightBlue,citecolor=MidnightBlue,urlcolor=MidnightBlue]{hyperref}

% ---- manuscript metadata -------------------------------------------------
\newcommand{\msid}[1]{\def\@msid{#1}}
\newcommand{\msfamily}[1]{\def\@msfamily{#1}}
\newcommand{\msdiscipline}[1]{\def\@msdiscipline{#1}}
\newcommand{\mstype}[1]{\def\@mstype{#1}}
\newcommand{\msstatus}[1]{\def\@msstatus{#1}}
\newcommand{\mskeywords}[1]{\def\@mskeywords{#1}}
\newcommand{\mslean}[1]{\def\@mslean{#1}}
\msid{}\msfamily{}\msdiscipline{}\mstype{}\msstatus{}\mskeywords{}\mslean{}

\author{Situationist AI}
\date{Preprint, 6 October 2026}

\renewcommand{\maketitle}{%
  \thispagestyle{plain}%
  \begin{center}
    {\small\scshape Situationist AI $\cdot$ Philosophy collection\par}
    \vspace{1.6em}
    {\LARGE\bfseries \@title\par}
    \vspace{1em}
    {\large \@author\par}
    \vspace{0.4em}
    {\small \@date\ifx\@msstatus\@empty\else\ $\cdot$ \@msstatus\fi\par}
    \vspace{0.6em}
    {\footnotesize Manuscript \@msid{} $\cdot$ Family \@msfamily{} $\cdot$ \@msdiscipline{} $\cdot$ \@mstype\par}
    \ifx\@mslean\@empty\else
      {\footnotesize Formalization: \texttt{\@mslean}\par}
    \fi
  \end{center}
  \vspace{1.2em}}

\renewenvironment{abstract}{%
  \begin{center}\begin{minipage}{0.86\textwidth}\small
  \noindent\textbf{Abstract.}\ }{%
  \ifx\@mskeywords\@empty\else\par\medskip\noindent\textbf{Keywords.}\ \@mskeywords\fi
  \end{minipage}\end{center}\vspace{1em}}

% ---- headers -------------------------------------------------------------
\pagestyle{fancy}
\fancyhf{}
\fancyhead[L]{\footnotesize\scshape Situationist AI}
\fancyhead[R]{\footnotesize \@msid}
\fancyfoot[C]{\footnotesize\thepage}
\renewcommand{\headrulewidth}{0.3pt}
\fancypagestyle{plain}{\fancyhf{}\fancyfoot[C]{\footnotesize\thepage}\renewcommand{\headrulewidth}{0pt}}

% ---- theorem environments ------------------------------------------------
\theoremstyle{plain}
\newtheorem{theorem}{Theorem}[section]
\newtheorem{lemma}[theorem]{Lemma}
\newtheorem{proposition}[theorem]{Proposition}
\newtheorem{corollary}[theorem]{Corollary}
\theoremstyle{definition}
\newtheorem{definition}[theorem]{Definition}
\newtheorem{principle}{Principle}
\renewcommand{\theprinciple}{P\arabic{principle}}
\newtheorem{assumption}[theorem]{Assumption}
\newtheorem{objection}{Objection}
\theoremstyle{remark}
\newtheorem{remark}[theorem]{Remark}
\newtheorem*{reply}{Reply}

% ---- listings for Lean -----------------------------------------------------
\lstdefinelanguage{Lean}{morekeywords={theorem,lemma,def,abbrev,axiom,namespace,end,fun,by,intro,exact,obtain,have,open,import},
  sensitive=true,morecomment=[l]{--},morecomment=[s]{/-}{-/},morestring=[b]"}
\lstset{language=Lean,basicstyle=\footnotesize\ttfamily,columns=fullflexible,keepspaces=true,
  keywordstyle=\bfseries,commentstyle=\itshape\color{gray},frame=lines,framesep=4pt,
  literate={→}{{$\to$}}1 {∀}{{$\forall$}}1 {∃}{{$\exists$}}1 {∧}{{$\wedge$}}1 {¬}{{$\neg$}}1 {⟨}{{$\langle$}}1 {⟩}{{$\rangle$}}1 {≠}{{$\neq$}}1 {≥}{{$\geq$}}1 {≤}{{$\leq$}}1 {↔}{{$\leftrightarrow$}}1 {∨}{{$\vee$}}1 {←}{{$\leftarrow$}}1 {·}{{$\cdot$}}1 {ρ}{{$\rho$}}1 {σ}{{$\sigma$}}1 {₀}{{$_0$}}1 {₁}{{$_1$}}1 {∈}{{$\in$}}1 {×}{{$\times$}}1 {≃}{{$\simeq$}}1}

\setlist{itemsep=2pt,topsep=4pt}
\newcommand{\nec}{\mathord{\Box}}
\newcommand{\pos}{\mathord{\Diamond}}
