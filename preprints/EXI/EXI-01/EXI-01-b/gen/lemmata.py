"""The lemmata of EXI-01-a, as segmented in the Commentary (EXI-01-b).

Each entry is (number, quotation). Quotations are written in the TeX of the
source (math in $...$, \\emph{...}, \\citep{...}); generate.py normalizes both
the quotation and the source and checks that every quotation occurs verbatim
in EXI-01-a.  Sentence lemmata have integer numbers; phrase lemmata are
numbered n.k under their sentence.
"""

LEMMATA = [
    ("1", r"On the Meaning of Life"),

    ("2", r"A life $L$ is \emph{meaningful to degree $d$} if $d$ is the extent to which $L$ consists in active engagement with projects of objective worth \citep{Wolf2010}."),
    ("2.1", r"A life $L$"),
    ("2.2", r"is \emph{meaningful to degree $d$}"),
    ("2.3", r"if $d$ is the extent to which"),
    ("2.4", r"$L$ consists in"),
    ("2.5", r"active engagement"),
    ("2.6", r"with projects"),
    ("2.7", r"of objective worth"),
    ("2.8", r"\citep{Wolf2010}"),

    ("3", r"There exist projects of objective worth: projects whose value does not depend on the attitudes of those engaged in them \citep{Metz2013}."),
    ("3.1", r"There exist"),
    ("3.2", r"projects of objective worth: projects whose value"),
    ("3.3", r"does not depend on"),
    ("3.4", r"the attitudes of those engaged in them"),
    ("3.5", r"\citep{Metz2013}"),

    ("4", r"For every agent capable of intentional action, there is at least one project of objective worth in which she is able to engage."),
    ("4.1", r"For every agent"),
    ("4.2", r"capable of intentional action"),
    ("4.3", r"there is at least one project of objective worth"),
    ("4.4", r"in which she is able to engage"),

    ("5", r"For every such agent, a life of positive meaning is available."),
    ("5.1", r"For every such agent"),
    ("5.2", r"a life of positive meaning"),
    ("5.3", r"is available"),

    ("6", r"By Assumption 3, there is a project $p$ of objective worth in which the agent can engage."),
    ("7", r"A life that includes engagement with $p$ consists, to some positive extent, in active engagement with a project of objective worth."),
    ("7.1", r"A life that includes engagement with $p$"),
    ("7.2", r"consists, to some positive extent, in"),
    ("8", r"By Definition 1, it is meaningful to a positive degree."),

    ("9", r"The theorem answers the question of what the meaning of life is, and of whether meaning is available to everyone."),
    ("9.1", r"The theorem answers the question of what the meaning of life is"),
    ("9.2", r"and of whether meaning is available to everyone"),
    ("10", r"It does not answer the question of whether any particular life is meaningful, which depends on what is done with it."),
    ("11", r"Nor does it answer the sceptical challenge that, \emph{sub specie aeternitatis}, nothing matters \citep{Nagel1971}: Assumption 2 denies the premise of that challenge rather than refuting it."),
    ("11.1", r"the sceptical challenge"),
    ("11.2", r"\emph{sub specie aeternitatis}"),
    ("11.3", r"nothing matters"),
    ("11.4", r"Assumption 2 denies the premise of that challenge rather than refuting it"),
    ("12", r"A defence of Assumption 2, and a discussion of the absurd, are given in the commentary (EXI-01-b)."),
]

# Sentence lemmata grouped by the numbered statement of EXI-01-a they belong to.
STATEMENTS = [
    ("Title", ["1"]),
    ("Definition 1", ["2"]),
    ("Assumption 2", ["3"]),
    ("Assumption 3", ["4"]),
    ("Theorem 4", ["5"]),
    ("Proof", ["6", "7", "8"]),
    ("Remark 5", ["9", "10", "11", "12"]),
]
