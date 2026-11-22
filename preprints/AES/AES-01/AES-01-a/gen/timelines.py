"""Documented histories of selected cases, as sequences of artworld events.

Event codes (Appendix E of the manuscript):
  P  presentation by a participant          D  a single agent's declaration
  R  refusal by a venue or authority         S  a sale
  a  adverse critical engagement             f  favourable critical engagement
  m  engagement with assessments divided on merit
  v  the practice divided on whether to engage the object as a candidate
  c  engagement as curiosity, news or specimen only
  0  an event with no bearing on the conditions (making, death, damage,
     legal proceedings)
Each history begins at the first index at which the object stands in
relation to an artworld; earlier stages are recorded in the note.
"""

TIMELINES = [
  ("FTN", r"\emph{Fountain}", ["FT1", "FT2", "FTR", "FT3"], [
    ("April 1917", "P", r"submitted to the Society of Independent Artists"),
    ("April 1917", "R", r"not shown by the Society"),
    ("May 1917", "v", r"photograph and editorial in \emph{The Blind Man}"),
    ("1917--1950", "0", r"original object lost"),
    ("1950", "P", r"first authorized replica"),
    ("1950s on", "m", r"interpreted and assessed in criticism and art history"),
    ("1964", "S", r"edition produced with Arturo Schwarz, sold"),
    ("1993, 2006", "c", r"Pinoncelli's attacks on replicas reported"),
  ], r"Duchamp's signature (a single declaration) is part of the first presentation."),
  ("MAN", r"\emph{Le D\'ejeuner sur l'herbe}", ["MN0", "MN1"], [
    ("1863", "P", r"submitted to the Salon"),
    ("1863", "R", r"rejected by the jury"),
    ("1863", "P", r"shown at the Salon des Refus\'es"),
    ("1863", "a", r"ridicule and scandal"),
  ], ""),
  ("ALT", r"Altamira", ["AL1", "AL2"], [
    ("1880", "P", r"published by Sanz de Sautuola"),
    ("1880s", "R", r"antiquity rejected by leading prehistorians"),
    ("1902", "f", r"Cartailhac's retraction; antiquity accepted"),
  ], r"Before the cave's discovery the paintings stood in no relation to an artworld."),
  ("LAS", r"Lascaux", ["LX1", "LX2"], [
    ("1940", "P", r"discovery and publication"),
    ("1955", "f", r"Bataille's book on the birth of art"),
    ("1963", "0", r"closed to visitors"),
    ("1983", "P", r"replica opened"),
  ], r"At the time of making there was no artworld (LX1); uptake is dated here by its best-known document, not by its first."),
  ("WHI", r"\emph{Nocturne in Black and Gold}", ["WN1"], [
    ("1877", "P", r"exhibited at the Grosvenor Gallery"),
    ("1877", "a", r"Ruskin's attack in \emph{Fors Clavigera}"),
    ("1878", "0", r"libel verdict: a farthing in damages"),
  ], ""),
  ("VGO", r"Van Gogh", ["VN1"], [
    ("1890", "P", r"exhibited with Les XX, Brussels"),
    ("1890", "f", r"Aurier's article in the \emph{Mercure de France}"),
    ("1890", "S", r"\emph{The Red Vineyard} bought by Anna Boch"),
  ], ""),
  ("BRA", r"\emph{Bird in Space}", ["BX1"], [
    ("1926", "P", r"imported for exhibition in New York"),
    ("1926", "R", r"customs refuse it entry as a work of art"),
    ("1926--1928", "f", r"critics and artists testify to its standing as sculpture"),
    ("1928", "0", r"Customs Court rules that it is a work of art"),
  ], r"Brancusi's earlier \emph{Birds} had already been engaged by critics and collectors; the history records only this object's entry."),
  ("VMG", r"\emph{Christ and the Disciples at Emmaus}", ["VG1", "VG2"], [
    ("1937", "P", r"acquired and shown by the Museum Boijmans"),
    ("1937", "f", r"acclaimed by Bredius as a Vermeer"),
    ("1945", "0", r"van Meegeren's confession"),
    ("1947", "0", r"trial and conviction"),
    ("after 1947", "a", r"discussed as a forgery; faults remarked"),
  ], ""),
  ("EQ8", r"\emph{Equivalent VIII}", ["EQ1", "EQ2"], [
    ("1972", "S", r"bought by the Tate Gallery"),
    ("1972", "P", r"in the Tate's collection"),
    ("1972", "f", r"engaged within the practice of minimal sculpture"),
    ("1976", "a", r"press controversy"),
    ("1976", "0", r"defaced with dye"),
  ], ""),
  ("DRG", r"Darger", ["DG1", "DG2"], [
    ("to 1972", "0", r"the work made and shown to no one"),
    ("1972", "0", r"found by Nathan Lerner"),
    ("1973", "0", r"Darger dies"),
    ("later", "P", r"exhibited"),
    ("later", "f", r"engaged by curators, critics, historians"),
  ], ""),
  ("MAI", r"Maier", ["VV1", "VV2"], [
    ("to 2007", "0", r"photographs taken, mostly unprinted"),
    ("2007", "S", r"negatives bought at auction"),
    ("2009", "0", r"Maier dies"),
    ("later", "P", r"printed, exhibited and published"),
    ("later", "f", r"engaged by curators and critics"),
  ], r"The sale of 2007 is a sale of the contents of a storage locker, not of works."),
  ("TRL", r"\emph{The Trial}", ["KF1"], [
    ("1924", "0", r"Kafka dies, asking that his papers be burned"),
    ("1925", "P", r"published by Brod"),
    ("later", "f", r"engaged as literature"),
  ], ""),
  ("NKF", r"Kongo power figure", ["NK0", "NK1", "NK2"], [
    ("late 19th c.", "0", r"collected as an ethnographic specimen"),
    ("1984", "P", r"exhibited at the Museum of Modern Art"),
    ("1984", "m", r"engaged as a work; exhibition criticized"),
  ], r"In use (NK0) the figure stood in no relation to an artworld."),
  ("RUB", r"Rublev, \emph{Trinity}", ["RB1", "RB2"], [
    ("1929", "P", r"transferred to the Tretyakov Gallery"),
    ("after 1929", "f", r"exhibited and studied as a masterpiece"),
  ], r"In liturgical use (RB1) there was no artworld at the index."),
  ("CMD", r"\emph{Comedian}", ["CM1", "CM2", "CM4"], [
    ("2019", "P", r"shown at Art Basel Miami Beach"),
    ("2019", "S", r"editions sold"),
    ("2019", "m", r"engaged as a work, largely adversely"),
    ("2019", "0", r"banana eaten and replaced"),
    ("2024", "S", r"sold at Sotheby's"),
  ], ""),
  ("BAN", r"\emph{Girl with Balloon}", ["BK1"], [
    ("2018", "P", r"offered at auction"),
    ("2018", "S", r"sold"),
    ("2018", "0", r"partly shredded"),
    ("2018", "m", r"engaged as a work and as a comment on the market"),
    ("2021", "S", r"sold again"),
  ], r"The canvas had been engaged as a work before the auction; the history begins with the sale."),
  ("BEL", r"\emph{Edmond de Belamy}", ["AI1"], [
    ("2018", "P", r"offered at Christie's"),
    ("2018", "S", r"sold far above estimate"),
    ("2018", "v", r"discussed as a work and as a technological event"),
  ], ""),
  ("LIV", r"A signed person", ["MZ4"], [
    ("1961", "D", r"signed by Manzoni"),
    ("1961", "P", r"certificate issued"),
    ("1961 on", "c", r"documented as part of the series"),
  ], r"The series (MZ3) is taken up; the person, as an object, is not."),
  ("YEL", r"Umanets's inscription", ["YW1"], [
    ("2012", "D", r"inscription on the Rothko"),
    ("2012", "P", r"public statement presenting the act"),
    ("2012", "c", r"reported as vandalism"),
    ("2013", "0", r"conviction for criminal damage"),
  ], ""),
]
