"""Hand-curated catalogue of boundary and test cases for AES-01-a.

Each entry is an *episode*: an object at a stage of its history, relative to
the artworld (if any) in which it is placed at that stage.  Fields:

  id       identifier (letters and a digit; no hyphen)
  grp      R readymades, I indiscernibles and thought experiments,
           P performance, music and Fluxus, M minimal and conceptual works,
           A adverse reception, O outsider and posthumous, H before artworlds
           and cult objects, N non-human makers, F forgery, C contemporary
           market, X machine outputs, S schematic cases
  name     short name (LaTeX)
  stage    the stage of the object's history encoded (LaTeX)
  facts    documented facts, in our own words (LaTeX); only facts of record
  cite     citation keys of scholarly sources for the case (may be empty)
  hyp      True for thought experiments and schematic cases
  aw       an artworld exists in which the object is placed at this stage
  pres     'no' | 'maker' | 'other'      (Definition 2.1)
  by       presenter and venue (LaTeX), or None
  crit     'none'      no engagement by the critical practice
           'curio'     engaged, but not as a candidate (as a curiosity,
                       document, specimen, stunt or technical event)
           'refused'   declined as a candidate by the venue of presentation
           'adverse'   engaged as a candidate and assessed unfavourably
           'favourable' engaged as a candidate and assessed favourably
           'mixed'     engaged as a candidate, assessments divided on merit
           'divided'   the practice divided on whether to engage it as a
                       candidate at all                  (Definitions 2.2, 2.4)
  mkt      'none' | 'sold' | 'high'      market uptake (Definition 2.5)
  decl     a single agent declared the object art (signature, title,
           certificate, public statement)
  ae       Beardsley's aesthetic definition satisfied: 'Y' | 'N' | '?'
  lev      Levinson's intention for regard-as-a-work: 'Y' | 'N' | '?' | 'ur'
  g        Gaut's ten criteria, as a string of ten 0/1 in Gaut's order:
           positive aesthetic properties, expressive of emotion,
           intellectually challenging, formally complex and coherent,
           capacity to convey complex meanings, individual point of view,
           originality, high degree of skill, established art form,
           intention to make a work of art
  fn       intended to fulfil a function art has at the time (Stecker):
           'Y' | 'N' | '?'
  exc      achieves excellence in such a function (Stecker): 'Y' | 'N'
  narr     a Carroll-style identifying narrative to prior art is available:
           'Y' | 'N' | '?'
  note     ground of the uptake encoding (LaTeX)
"""

CASES = []


def E(id, grp, name, stage, facts, cite, aw, pres, by, crit, mkt, decl,
      ae, lev, g, fn, exc, narr, note, hyp=False):
    assert len(g) == 10 and set(g) <= {"0", "1"}, id
    assert pres in ("no", "maker", "other"), id
    assert crit in ("none", "curio", "refused", "adverse", "favourable",
                    "mixed", "divided"), id
    assert mkt in ("none", "sold", "high"), id
    assert ae in "YN?" and fn in "YN?" and exc in "YN" and narr in "YN?", id
    assert lev in ("Y", "N", "?", "ur"), id
    if not aw:
        assert pres == "no", id
    if pres == "no":
        assert crit == "none", id
    CASES.append(dict(id=id, grp=grp, name=name, stage=stage, facts=facts,
                      cite=cite, aw=aw, pres=pres, by=by, crit=crit, mkt=mkt,
                      decl=decl, ae=ae, lev=lev, g=g, fn=fn, exc=exc,
                      narr=narr, note=note, hyp=hyp))


# ===================================================================== R
E("FT1", "R", r"\emph{Fountain}", r"submission, April 1917",
  r"A porcelain urinal, turned on its back and signed \enquote{R. Mutt 1917}, was submitted to the first exhibition of the Society of Independent Artists in New York, whose rules promised to hang the work of any member who paid the fee. The object was not shown.",
  ["deDuve1996"], True, "maker", r"Duchamp (as R. Mutt), Society of Independent Artists",
  "refused", "none", True, "N", "Y", "0010111001", "Y", "N", "Y",
  r"Declined as a candidate by the venue of presentation; no other engagement at this stage.")
E("FT2", "R", r"\emph{Fountain}", r"\emph{The Blind Man} no.~2, May 1917",
  r"The object was photographed by Alfred Stieglitz, and the photograph was reproduced in the second issue of \emph{The Blind Man}, a little magazine edited by Duchamp, Henri-Pierre Roch\'e and Beatrice Wood, with an unsigned editorial defending the submission.",
  [], True, "other", r"editors of \emph{The Blind Man}, through Stieglitz's photograph",
  "divided", "none", True, "N", "Y", "0010111001", "Y", "N", "Y",
  r"A defense from within the presenter's own circle; the wider practice had not yet engaged the object as a candidate.")
E("FT3", "R", r"\emph{Fountain}", r"critical reception from the 1950s",
  r"The original object was lost. From the 1950s the readymade became a central topic of criticism and art history, and \emph{Fountain} its paradigm; it has been interpreted and assessed, favourably and adversely, ever since.",
  ["deDuve1996", "Danto1981"], True, "other", r"exhibitions, art history, criticism",
  "mixed", "none", True, "N", "Y", "0010111011", "Y", "Y", "Y",
  r"Continuous engagement as a work, with assessments divided on merit.")
E("FTR", "R", r"\emph{Fountain}, replicas", r"1950 onward",
  r"From 1950 Duchamp authorized replicas, including an edition produced with Arturo Schwarz in 1964. The replicas are the objects now held in museums and exhibited, catalogued and interpreted as \emph{Fountain}; examples of the 1964 edition have been sold at auction for high prices.",
  [], True, "other", r"Duchamp's authorization; Galleria Schwarz; museums",
  "mixed", "high", True, "N", "Y", "0010111011", "Y", "Y", "Y",
  r"Taken up by the practice as instances of the work.")
E("FTU", "S", r"Urinal in a showroom", r"schematic",
  r"A urinal of the same model as the one Duchamp submitted, displayed for sale by a plumbing supplier. Nobody offers it to an artworld public.",
  [], True, "no", None, "none", "sold", False, "N", "N", "0000000000", "N", "N", "N",
  r"Not presented.", hyp=True)
E("BW1", "R", r"\emph{Bicycle Wheel}", r"1913; later replicas",
  r"A bicycle wheel mounted upside down on a kitchen stool, made by Duchamp in Paris in 1913 and later counted the first of his readymades. The original was lost and the work is known through later versions.",
  [], True, "maker", r"Duchamp; later exhibitions of the versions",
  "favourable", "sold", False, "N", "Y", "0010111001", "Y", "Y", "Y",
  r"Engaged as a work in the literature on the readymade.")
E("BR1", "R", r"\emph{Bottle Rack}", r"1914; later replicas",
  r"A galvanized iron bottle-drying rack bought by Duchamp in Paris in 1914 and chosen without alteration. The original was lost and the work is known through later versions.",
  [], True, "maker", r"Duchamp; later exhibitions of the versions",
  "favourable", "sold", False, "N", "Y", "0010111001", "Y", "Y", "Y",
  r"Engaged as a work in the literature on the readymade.")
E("SH1", "R", r"\emph{In Advance of the Broken Arm}", r"1915",
  r"A snow shovel bought in New York in 1915, inscribed with its title and hung from the ceiling.",
  [], True, "maker", r"Duchamp; later exhibitions of the versions",
  "favourable", "sold", True, "N", "Y", "0010111001", "Y", "N", "Y",
  r"Engaged as a work in the literature on the readymade.")
E("LH1", "R", r"\emph{L.H.O.O.Q.}", r"1919",
  r"A cheap reproduction of Leonardo's \emph{Mona Lisa} on which Duchamp drew a moustache and a goatee in pencil and wrote the title, whose letters, read aloud in French, make an indecent pun.",
  [], True, "maker", r"Duchamp", "mixed", "none", True, "N", "Y", "0010111001", "Y", "Y", "Y",
  r"Engaged as a work, assessed as wit and as provocation.")
E("UR1", "R", r"\emph{Unhappy Readymade}", r"1919",
  r"On the occasion of his sister Suzanne's marriage, Duchamp sent instructions that a geometry textbook be hung on a balcony so that the weather would work through its pages. The book did not survive; the work is known through a photograph and through Suzanne Duchamp's painting of it.",
  [], True, "other", r"Suzanne Duchamp, following Duchamp's instructions; later literature",
  "favourable", "none", False, "N", "Y", "0010110001", "Y", "N", "Y",
  r"Engaged as a work in the literature on the readymade, the object itself being lost.")

# ===================================================================== I
E("BB1", "I", r"\emph{Brillo Box (Soap Pads)}", r"Stable Gallery, 1964",
  r"Warhol exhibited plywood boxes, silkscreened to look like the cartons in which Brillo soap pads were shipped, at the Stable Gallery in New York in 1964. Danto's paper on the artworld took the case to show that what makes the difference between an artwork and a perceptually indiscernible thing cannot be seen.",
  ["Danto1964", "Danto1981"], True, "maker", r"Warhol, Stable Gallery, New York",
  "mixed", "high", False, "?", "Y", "0010111011", "Y", "Y", "Y",
  r"Engaged as a work from the first exhibition, assessed favourably and adversely.")
E("BB2", "I", r"Brillo carton", r"commercial packaging, 1960s",
  r"The commercial carton on which Warhol's boxes were modelled had been designed by James Harvey, a painter who worked as a commercial artist. It was produced in quantity and used for shipping.",
  [], True, "no", None, "none", "sold", False, "Y", "N", "1001001100", "N", "N", "N",
  r"Offered to customers as packaging, not to an artworld public as a candidate.")
E("RS1", "I", r"\emph{The Israelites Crossing the Red Sea}", r"thought experiment",
  r"The first of the red rectangles in Danto's imagined exhibition: a painting whose title tells us that the Israelites have crossed and the Egyptians are drowned.",
  ["Danto1981"], True, "maker", r"the artist, in Danto's imagined exhibition",
  "favourable", "none", True, "?", "Y", "0010110111", "Y", "N", "Y",
  r"Stipulated: engaged and interpreted as a work within the thought experiment.", hyp=True)
E("RS2", "I", r"\emph{Kierkegaard's Mood}", r"thought experiment",
  r"A red rectangle presented as a psychological portrait, indiscernible from the first.",
  ["Danto1981"], True, "maker", r"the artist, in Danto's imagined exhibition",
  "favourable", "none", True, "?", "Y", "0110110111", "Y", "N", "Y",
  r"Stipulated: engaged and interpreted as a work within the thought experiment.", hyp=True)
E("RS3", "I", r"\emph{Red Square}", r"thought experiment",
  r"A red rectangle presented as a witty landscape of Moscow, indiscernible from the others.",
  ["Danto1981"], True, "maker", r"the artist, in Danto's imagined exhibition",
  "favourable", "none", True, "?", "Y", "0010110111", "Y", "N", "Y",
  r"Stipulated: engaged and interpreted as a work within the thought experiment.", hyp=True)
E("RS4", "I", r"Red-lead surface", r"thought experiment",
  r"A surface painted with red lead which Danto includes among the indiscernibles as a mere thing, with no claim to be a work.",
  ["Danto1981"], True, "no", None, "none", "none", False, "N", "N", "0000000000", "N", "N", "N",
  r"Not offered as a candidate.", hyp=True)
E("RS5", "I", r"Giorgione's ground", r"thought experiment",
  r"A canvas grounded in red lead by Giorgione for a painting he did not execute, in Danto's list of indiscernibles.",
  ["Danto1981"], True, "no", None, "none", "none", False, "N", "N", "0000000100", "N", "N", "N",
  r"A stage in the making of an unexecuted work; not offered as a candidate.", hyp=True)

# ===================================================================== P
E("CG1", "P", r"Cage, \emph{4$'$33$''$}", r"premiere, 29 August 1952",
  r"First performed by David Tudor at the Maverick Concert Hall near Woodstock, New York. The pianist marked the beginning and end of each of the three movements by closing and opening the keyboard lid and played nothing; the audience heard the sounds of the hall and its surroundings.",
  ["Cage1961"], True, "maker", r"Cage, through Tudor's performance",
  "mixed", "none", False, "?", "Y", "0010111011", "Y", "Y", "Y",
  r"Engaged as a work from the premiere onward, with sharply divided assessments.")
E("RW1", "P", r"Rauschenberg, \emph{White Paintings}", r"1951",
  r"Panels painted with flat white house paint, made at Black Mountain College in 1951. Cage wrote of them as surfaces that receive light, shadows and dust, and cited them as a precedent for his silent piece.",
  ["Cage1961"], True, "maker", r"Rauschenberg; Cage's writings; later exhibitions",
  "mixed", "none", False, "?", "Y", "0010111011", "Y", "N", "Y",
  r"Engaged as works, notably in Cage's criticism.")
E("ED1", "P", r"\emph{Erased de Kooning Drawing}", r"1953",
  r"Rauschenberg obtained a drawing from Willem de Kooning and erased it over a period of weeks. Jasper Johns lettered the label giving the title, the artist and the date; the work is in the collection of the San Francisco Museum of Modern Art.",
  [], True, "maker", r"Rauschenberg; museum collection",
  "mixed", "none", True, "?", "Y", "0010111001", "Y", "Y", "Y",
  r"Engaged as a work and as a statement about authorship and erasure.")
E("YC1", "P", r"Young, \emph{Composition 1960 \#10}", r"1960",
  r"An event score by La Monte Young, dedicated to Robert Morris, whose entire text instructs the performer to draw a straight line and follow it.",
  [], True, "maker", r"Young; Fluxus performances and publications",
  "favourable", "none", True, "N", "Y", "0010111011", "Y", "N", "Y",
  r"Engaged as a work in the literature on Fluxus and event scores.")
E("BD1", "P", r"Brecht, \emph{Drip Music}", r"1959--1962",
  r"An event score by George Brecht in which water is dripped from a height into a vessel; performed at Fluxus concerts.",
  [], True, "maker", r"Brecht; Fluxus concerts", "favourable", "none", True, "?", "Y",
  "0010111011", "Y", "N", "Y", r"Engaged as a work in the literature on Fluxus.")
E("CP1", "P", r"Ono, \emph{Cut Piece}", r"Kyoto, 1964",
  r"First performed by Yoko Ono at the Yamaichi Concert Hall in Kyoto in 1964: the artist sat on the stage and members of the audience were invited to cut away pieces of her clothing with scissors.",
  [], True, "maker", r"Ono, in performance", "favourable", "none", False, "?", "Y",
  "0111111011", "Y", "Y", "Y", r"Engaged as a work; a reference point in the history of performance art.")
E("WB1", "P", r"Fluxus festival, Wiesbaden", r"September 1962",
  r"The Fluxus festival of new music organized by George Maciunas in Wiesbaden in 1962 included Philip Corner's \emph{Piano Activities}, in the course of whose performances a piano was taken apart. The festival drew hostile reactions from part of its audience and from the press.",
  [], True, "maker", r"Maciunas and the performers; Wiesbaden", "adverse", "none", False, "N", "Y",
  "0010110011", "Y", "N", "Y", r"Engaged as concerts and assessed unfavourably.")
E("TG1", "P", r"Tinguely, \emph{Homage to New York}", r"17 March 1960",
  r"A machine assembled from scrap and designed to destroy itself, performed in the sculpture garden of the Museum of Modern Art in New York. It caught fire and was finished off by firemen; fragments are in the museum's collection.",
  [], True, "maker", r"Tinguely, Museum of Modern Art", "mixed", "none", False, "?", "Y",
  "0010111011", "Y", "N", "Y", r"Engaged as a work at the event and in later criticism.")
E("RSP", "P", r"\emph{The Rite of Spring}", r"premiere, 29 May 1913",
  r"Stravinsky's ballet, with choreography by Nijinsky, was first performed by the Ballets Russes at the Th\'e\^atre des Champs-\'Elys\'ees in Paris. The performance was disrupted by uproar in the audience.",
  [], True, "maker", r"Ballets Russes, Paris", "mixed", "sold", False, "Y", "Y", "1111111111",
  "Y", "Y", "Y", r"Engaged as a work, assessed with hostility and enthusiasm.")

# ===================================================================== M
E("EQ1", "M", r"Andre, \emph{Equivalent VIII}", r"acquisition by the Tate, 1972",
  r"One of a series of floor sculptures by Carl Andre, each consisting of 120 firebricks arranged in a rectangle two layers deep; the Tate Gallery acquired \emph{Equivalent VIII} in 1972.",
  [], True, "other", r"Andre; Tate Gallery", "favourable", "sold", False, "N", "Y",
  "0010110011", "Y", "N", "Y", r"Engaged as a work within the practice of minimal sculpture.")
E("EQ2", "M", r"Andre, \emph{Equivalent VIII}", r"press controversy, 1976",
  r"In 1976 the purchase became the subject of a prolonged controversy in the British press, which presented it as a waste of public money on a pile of bricks; the work was defaced with dye while on display.",
  [], True, "other", r"Tate Gallery", "adverse", "sold", False, "N", "Y",
  "0010110011", "Y", "N", "Y", r"Engaged as a work and assessed unfavourably in public criticism.")
E("EQ3", "S", r"120 firebricks", r"schematic",
  r"A stack of 120 firebricks of the same kind, delivered to a building site.",
  [], True, "no", None, "none", "sold", False, "N", "N", "0000000000", "N", "N", "N",
  r"Not presented.", hyp=True)
E("MZ1", "M", r"Manzoni, \emph{Artist's Shit}", r"1961",
  r"Ninety tins, each labelled as containing thirty grams of the artist's excrement, which Manzoni proposed to sell at the current price of the same weight of gold. Examples are held in museum collections and have been sold at auction for high prices.",
  [], True, "maker", r"Manzoni; galleries and museums", "mixed", "high", True, "N", "Y",
  "0010111001", "Y", "N", "Y", r"Engaged as a work, centrally in criticism of the art market.")
E("MZ2", "M", r"Manzoni, \emph{Base of the World}", r"Herning, 1961",
  r"An iron block installed in a park in Herning, Denmark, bearing an inverted inscription, so that the block supports the whole earth as its plinth.",
  [], True, "maker", r"Manzoni, Herning", "favourable", "none", True, "N", "Y",
  "0010111001", "Y", "N", "Y", r"Engaged as a work in the literature on Manzoni.")
E("MZ3", "M", r"Manzoni, \emph{Living Sculptures}", r"the series, 1961",
  r"Manzoni signed the bodies of people and issued them certificates of authenticity declaring them works of art; the series is documented by the certificates and by photographs.",
  [], True, "maker", r"Manzoni, certificates and photographs", "favourable", "none", True, "N", "Y",
  "0010111001", "Y", "N", "Y", r"The series, as a gesture, is engaged as a work.")
E("MZ4", "M", r"A signed person", r"as an object, 1961 onward",
  r"One of the people Manzoni signed, considered as an object and apart from the series to which the signing belongs.",
  [], True, "maker", r"Manzoni, by signature and certificate", "curio", "none", True, "N", "Y",
  "0000000001", "Y", "N", "?", r"The practice engages the gesture and its documents, not the person as a candidate; our encoding.")
E("YK1", "M", r"Klein, \emph{The Void}", r"Iris Clert, Paris, 1958",
  r"Yves Klein exhibited the emptied gallery of Iris Clert in Paris, its walls painted white, with nothing on show.",
  [], True, "maker", r"Klein, Galerie Iris Clert", "mixed", "none", True, "?", "Y",
  "0010111001", "Y", "N", "Y", r"Engaged as a work and as a provocation.")
E("OT1", "M", r"Craig-Martin, \emph{An Oak Tree}", r"1973",
  r"A glass of water on a glass shelf, accompanied by a printed text in question-and-answer form in which the artist asserts that he has changed the glass of water into an oak tree without altering its accidents.",
  [], True, "maker", r"Craig-Martin; galleries", "mixed", "sold", True, "N", "Y",
  "0010111001", "Y", "N", "Y", r"Engaged as a work about the conditions of art status.")
E("BS1", "M", r"Malevich, \emph{Black Square}", r"0,10 exhibition, Petrograd, 1915",
  r"A black square on a white ground, shown at the exhibition \enquote{0,10} in Petrograd in 1915, hung across the upper corner of the room in the position traditionally given to an icon.",
  [], True, "maker", r"Malevich, \enquote{0,10} exhibition", "mixed", "none", False, "?", "Y",
  "0110111111", "Y", "Y", "Y", r"Engaged as a work, assessed with hostility and with veneration.")
E("SL1", "M", r"Levine, \emph{After Walker Evans}", r"1981",
  r"Sherrie Levine rephotographed reproductions of photographs by Walker Evans and exhibited the results under her own name and a title acknowledging their source.",
  [], True, "maker", r"Levine; gallery exhibition", "mixed", "sold", True, "N", "Y",
  "0010111011", "Y", "N", "Y", r"Engaged as a work of appropriation, assessed for and against.")

# ===================================================================== A
E("WN1", "A", r"Whistler, \emph{Nocturne in Black and Gold}", r"Grosvenor Gallery, 1877",
  r"Exhibited at the Grosvenor Gallery in London in 1877, the picture of fireworks over Cremorne Gardens was attacked by Ruskin in \emph{Fors Clavigera} as an insult to the public. Whistler sued for libel and in 1878 was awarded a farthing in damages.",
  ["Whistler1890"], True, "maker", r"Whistler, Grosvenor Gallery", "adverse", "sold", False, "Y", "Y",
  "1100111111", "Y", "Y", "Y", r"Engaged as a work by the leading critic of the day and assessed unfavourably.")
E("MN0", "A", r"Manet, \emph{Le D\'ejeuner sur l'herbe}", r"Salon jury, 1863",
  r"Submitted to the Paris Salon of 1863 and rejected by its jury, together with an unusually large number of other submissions.",
  [], True, "maker", r"Manet, Salon of 1863", "refused", "none", False, "Y", "Y",
  "1110111111", "Y", "Y", "Y", r"Declined by the venue of presentation; no other engagement at this stage.")
E("MN1", "A", r"Manet, \emph{Le D\'ejeuner sur l'herbe}", r"Salon des Refus\'es, 1863",
  r"After protests against the jury, an exhibition of rejected works was authorized by Napoleon III. Manet's picture was shown there and became the object of ridicule and scandal.",
  [], True, "other", r"Salon des Refus\'es", "adverse", "none", False, "Y", "Y",
  "1110111111", "Y", "Y", "Y", r"Engaged as a work and assessed unfavourably by most who wrote on it.")
E("IM1", "A", r"Monet, \emph{Impression, Sunrise}", r"exhibition of 1874",
  r"Shown at the first exhibition of the independent group that came to be called the Impressionists, held in 1874 in the former studio of the photographer Nadar. The critic Louis Leroy's mocking review took the picture's title as the name of the group.",
  [], True, "maker", r"Soci\'et\'e anonyme exhibition, Paris", "adverse", "none", False, "Y", "Y",
  "1100111111", "Y", "Y", "Y", r"Engaged as a work and assessed unfavourably in the review that named the movement.")
E("MB1", "A", r"Museum of Bad Art", r"from 1994",
  r"A collection founded in 1994 in Dedham, Massachusetts, which exhibits paintings, many acquired from thrift shops or salvaged from refuse, selected for their badness and displayed with commentary on their failures.",
  [], True, "other", r"Museum of Bad Art", "adverse", "none", False, "Y", "?",
  "0100010011", "?", "N", "?", r"Engaged as works and assessed unfavourably, by design.")
E("TE1", "A", r"Emin, \emph{My Bed}", r"Turner Prize exhibition, 1999",
  r"Tracey Emin's unmade bed with the debris around it was shown at the Tate Gallery as part of the Turner Prize exhibition in 1999 and was widely derided in the press. It was sold at Christie's in London in 2014 for about two and a half million pounds.",
  [], True, "maker", r"Emin; Tate Gallery", "mixed", "high", False, "N", "Y",
  "0110111001", "Y", "N", "Y", r"Engaged as a work and assessed with hostility and with praise.")

# ===================================================================== O
E("DG1", "O", r"Darger, \emph{In the Realms of the Unreal}", r"in the artist's lifetime",
  r"Henry Darger, a hospital custodian in Chicago, wrote a narrative of many thousands of pages and made several hundred large illustrations for it in his room, showing them to no one.",
  [], True, "no", None, "none", "none", False, "Y", "?", "1111111110", "?", "Y", "N",
  r"Not offered to anyone.")
E("DG2", "O", r"Darger, \emph{In the Realms of the Unreal}", r"after 1972",
  r"When Darger moved to a care home in 1972, his landlord, the photographer Nathan Lerner, found the work in his room. Darger died in 1973. The illustrations were later exhibited widely and are held in collections, among them that of the American Folk Art Museum in New York.",
  [], True, "other", r"Nathan Lerner; museums and exhibitions", "favourable", "high", False, "Y", "?",
  "1111111110", "?", "Y", "Y", r"Engaged as works by curators, critics and art historians.")
E("WF1", "O", r"W\"olfli", r"from 1921",
  r"Adolf W\"olfli, a patient at the Waldau psychiatric clinic near Bern, produced a vast body of drawings and writings. His psychiatrist Walter Morgenthaler published a monograph on him in 1921 presenting him as an artist; his work is now held by a foundation at the Kunstmuseum Bern.",
  ["Morgenthaler1921"], True, "other", r"Morgenthaler's monograph; later exhibitions", "favourable", "high", False, "Y", "?",
  "1111111110", "?", "Y", "Y", r"Engaged as works from the 1920s, centrally in the discussion of art brut.")
E("PZ1", "O", r"Prinzhorn collection", r"as clinical material, c.~1920",
  r"The psychiatrist Hans Prinzhorn assembled at the Heidelberg psychiatric clinic a large collection of images made by patients of psychiatric institutions and studied it in a book of 1922 whose title speaks of the image-making, not the art, of the mentally ill.",
  ["Prinzhorn1922"], True, "no", None, "none", "none", False, "?", "?", "1111110000", "?", "N", "N",
  r"Collected and studied as clinical material, not offered to an artworld public.")
E("PZ2", "O", r"Prinzhorn collection", r"later exhibitions",
  r"Works from the collection have since been exhibited in art museums and discussed as art, and the collection has its own museum in Heidelberg.",
  [], True, "other", r"art museums", "favourable", "none", False, "?", "?", "1111110000",
  "?", "Y", "Y", r"Engaged as works by curators and critics.")
E("CH1", "O", r"Cheval, \emph{Palais Id\'eal}", r"Hauterives, 1879--1912",
  r"The postman Ferdinand Cheval built a fantastic palace of stones gathered on his rounds at Hauterives in the Dr\^ome over some thirty years. It was admired by the Surrealists and was protected as a historic monument in 1969.",
  [], True, "maker", r"Cheval, who opened it to visitors; later the Surrealists", "favourable", "none", False, "Y", "?",
  "1111111100", "Y", "Y", "Y", r"Engaged as a work by artists and critics.")
E("VV1", "O", r"Maier, photographs", r"in the photographer's lifetime",
  r"Vivian Maier, who worked for decades as a nanny in Chicago, took a very large number of street photographs, most of which she never printed and showed to no one.",
  [], True, "no", None, "none", "none", False, "?", "?", "1101111110", "?", "Y", "N",
  r"Not offered to anyone.")
E("VV2", "O", r"Maier, photographs", r"after 2007",
  r"In 2007 John Maloof bought a large part of her negatives at an auction of the contents of a storage locker. Maier died in 2009. The photographs have since been printed, exhibited and published, and were the subject of a documentary film in 2013.",
  [], True, "other", r"John Maloof; exhibitions and publications", "favourable", "high", False, "?", "?",
  "1101111110", "?", "Y", "Y", r"Engaged as works by curators and critics, with some dissent on their editing.")
E("DK1", "O", r"Dickinson, poems", r"posthumous publication, 1890",
  r"Emily Dickinson published only a handful of poems in her lifetime, anonymously. After her death in 1886 a selection edited by Mabel Loomis Todd and Thomas Wentworth Higginson was published in 1890.",
  [], True, "other", r"Todd and Higginson; publication", "favourable", "sold", False, "Y", "?",
  "1111111111", "?", "Y", "Y", r"Engaged as literature from the first posthumous publication.")
E("CD1", "S", r"A child's drawing", r"schematic",
  r"A drawing made by a child and given to her parents, who keep it on the kitchen door.",
  [], True, "no", None, "none", "none", False, "Y", "N", "1100010000", "N", "N", "N",
  r"Offered within a family, not to an artworld public.", hyp=True)

# ===================================================================== H
E("LX1", "H", r"Lascaux", r"at the time of making",
  r"The paintings and engravings of animals in the cave of Lascaux in the Dordogne are commonly dated to about seventeen thousand years ago. Whatever practice they belonged to, it was not one of presenting objects for appreciation and criticism as candidates of the kind we call art.",
  [], False, "no", None, "none", "none", False, "?", "ur", "1101101110", "?", "Y", "N",
  r"No artworld at this index.")
E("LX2", "H", r"Lascaux", r"after 1940",
  r"The cave was discovered in 1940 and the paintings were published, photographed, and discussed as the beginnings of art, notably by Georges Bataille in 1955. It was closed to visitors in 1963; a replica of part of it opened nearby in 1983.",
  ["Bataille1955"], True, "other", r"archaeologists, publications, replicas", "favourable", "none", False, "?", "ur",
  "1101101110", "?", "Y", "?", r"Engaged as works by art historians and critics.")
E("AL1", "H", r"Altamira", r"publication, 1880",
  r"Marcelino Sanz de Sautuola published the painted ceiling of the cave of Altamira in Cantabria in 1880, attributing it to the Palaeolithic. Leading prehistorians rejected the attribution and suspected a recent fabrication.",
  ["Cartailhac1902"], True, "other", r"Sanz de Sautuola's publication", "refused", "none", False, "?", "ur",
  "1101101110", "?", "Y", "?", r"Declined by the relevant experts, on grounds of authenticity.")
E("AL2", "H", r"Altamira", r"after 1902",
  r"After further discoveries of decorated caves in France, \'Emile Cartailhac, among the most prominent of the sceptics, published in 1902 a retraction of his doubts, and the antiquity of the paintings was accepted.",
  ["Cartailhac1902"], True, "other", r"prehistorians, art historians", "favourable", "none", False, "?", "ur",
  "1101101110", "?", "Y", "?", r"Engaged as works once their antiquity was accepted.")
E("CV1", "H", r"Chauvet", r"after 1994",
  r"The cave of Chauvet in the Ard\`eche, discovered in 1994, contains paintings dated to more than thirty thousand years ago. They were the subject of a film by Werner Herzog in 2010, and a replica of the cave opened in 2015.",
  [], True, "other", r"archaeologists, film, replica", "favourable", "none", False, "?", "ur",
  "1101101110", "?", "Y", "?", r"Engaged as works by art historians and critics.")
E("RB1", "H", r"Rublev, \emph{Trinity}", r"in liturgical use",
  r"The icon of the Trinity painted by Andrei Rublev in the early fifteenth century for the Trinity monastery of St Sergius. The Stoglav Council of 1551 prescribed his manner as a model for icons of the Trinity: the icon was judged by its fidelity to a canon of devotional images.",
  ["Belting1994"], False, "no", None, "none", "none", False, "?", "Y", "1101101111", "N", "Y", "?",
  r"The practice was devotional; no artworld at this index.")
E("RB2", "H", r"Rublev, \emph{Trinity}", r"in the Tretyakov Gallery",
  r"The icon was transferred to the Tretyakov Gallery in Moscow in 1929, where it has been exhibited and studied as a masterpiece of Russian painting.",
  ["Belting1994"], True, "other", r"Tretyakov Gallery", "favourable", "none", False, "?", "Y",
  "1101101111", "N", "Y", "Y", r"Engaged as a work by art historians.")
E("NK0", "H", r"Kongo power figure", r"in use",
  r"A carved wooden figure of the type called \emph{nkisi nkondi}, into which nails and blades were driven in the course of oaths and rites.",
  [], False, "no", None, "none", "none", False, "?", "?", "1101100110", "N", "Y", "N",
  r"The practice was ritual; no artworld at this index.")
E("NK1", "H", r"Kongo power figure", r"ethnographic specimen",
  r"Many such figures were taken to Europe from the late nineteenth century and catalogued in ethnographic museums as specimens of material culture.",
  [], True, "no", None, "none", "sold", False, "?", "N", "1101100110", "N", "Y", "N",
  r"Collected and displayed as specimens, not offered as candidates.")
E("NK2", "H", r"Kongo power figure", r"art museums; MoMA, 1984",
  r"Such figures are now held and exhibited by art museums. In 1984 the Museum of Modern Art in New York showed objects from African, Oceanic and other traditions beside modern works in an exhibition on primitivism in twentieth-century art, which was sharply criticized for presenting them through the eyes of modern artists.",
  ["Rubin1984", "McEvilley1984"], True, "other", r"Museum of Modern Art; art museums", "mixed", "high", False, "?", "N",
  "1101100110", "N", "Y", "Y", r"Engaged as works; the terms of the engagement disputed.")

# ===================================================================== N
E("BT1", "N", r"Betsy's paintings", r"museum of natural history",
  r"Dickie considers paintings made by a chimpanzee called Betsy, displayed in a museum of natural history as exhibits about animal behavior.",
  ["Dickie1974"], True, "no", None, "none", "none", False, "N", "N", "1000000000", "N", "N", "N",
  r"Displayed as specimens, not offered as candidates.", hyp=True)
E("BT2", "N", r"Betsy's paintings", r"hung in an art museum",
  r"Dickie's contrasting case: the same paintings hung in an art museum by someone acting on behalf of the artworld. Dickie holds that they would then be art.",
  ["Dickie1974"], True, "other", r"the museum's director", "none", "none", False, "N", "Y", "1000000000",
  "N", "N", "N", r"Stipulated only as presented; no critical engagement is described.", hyp=True)
E("CO1", "N", r"Congo's paintings", r"late 1950s; auction 2005",
  r"Paintings made by a chimpanzee called Congo at London Zoo, studied by the zoologist Desmond Morris in his book on the biology of art. They were exhibited in London in the 1950s; in 2005 three were sold at auction.",
  ["Morris1962"], True, "other", r"Desmond Morris; exhibition", "curio", "sold", False, "N", "Y",
  "1000000000", "N", "N", "N", r"Engaged chiefly as evidence about animal behavior and as a curiosity; our encoding.")
E("NS1", "N", r"The macaque selfie", r"2011; litigation to 2018",
  r"A crested macaque in Sulawesi triggered the camera of the photographer David Slater, producing self-portraits that circulated widely. A suit brought in the macaque's name was dismissed, the Court of Appeals for the Ninth Circuit holding in 2018 that animals cannot sue for copyright infringement under the Copyright Act.",
  [], True, "other", r"Slater, in publications", "curio", "sold", False, "N", "N",
  "1000000000", "N", "N", "N", r"Engaged as news, wildlife photography and a legal question; our encoding.")
E("DW0", "N", r"Driftwood", r"on the beach",
  r"A piece of driftwood of striking shape, lying on a beach, the stock example in the debate over whether art must be an artefact.",
  ["Dickie1974"], True, "no", None, "none", "none", False, "N", "N", "1001000000", "N", "N", "N",
  r"Not presented.", hyp=True)
E("DW1", "N", r"Driftwood", r"exhibited",
  r"The same piece, picked up and exhibited in a gallery as sculpture and reviewed as such.",
  ["Dickie1974"], True, "other", r"the finder, in a gallery", "favourable", "sold", False, "N", "Y",
  "1001000010", "N", "N", "Y", r"Stipulated: reviewed as sculpture.", hyp=True)

# ===================================================================== F
E("VG1", "F", r"\emph{Christ and the Disciples at Emmaus}", r"as a Vermeer, 1937",
  r"A painting by Han van Meegeren acclaimed by the Vermeer scholar Abraham Bredius as an early masterpiece of Vermeer and acquired for the Museum Boijmans in Rotterdam.",
  ["Bredius1937"], True, "other", r"Bredius; Museum Boijmans", "favourable", "high", False, "Y", "Y",
  "1110001111", "Y", "N", "Y", r"Engaged as a work, under a false attribution.")
E("VG2", "F", r"\emph{Christ and the Disciples at Emmaus}", r"after 1945",
  r"Van Meegeren's confession in 1945, his painting of a further picture under supervision, and his trial in 1947 established the attribution. The painting is now discussed as a forgery, and its faults are commonly remarked.",
  [], True, "other", r"Museum Boijmans; literature on forgery", "adverse", "none", False, "Y", "Y",
  "1100001111", "Y", "N", "Y", r"Engaged as a work, now assessed unfavourably.")

# ===================================================================== C
E("CM1", "C", r"Cattelan, \emph{Comedian}", r"Art Basel Miami Beach, 2019",
  r"A banana fixed to a wall with grey duct tape, shown by the gallery Perrotin in 2019; editions were sold for sums reported at \$120{,}000 and above. During the fair the artist David Datuna removed the banana and ate it, and the gallery replaced it.",
  [], True, "maker", r"Cattelan, Perrotin, Art Basel Miami Beach", "mixed", "high", False, "N", "Y",
  "0010111001", "Y", "N", "Y", r"Engaged as a work, much of the criticism adverse.")
E("CM2", "C", r"\emph{Comedian}, replacement banana", r"2019 onward",
  r"The work is sold as a certificate with instructions for its installation; the banana is perishable and is replaced as needed, as it was after it had been eaten.",
  [], True, "other", r"the gallery, following the instructions", "mixed", "high", False, "N", "Y",
  "0010111001", "Y", "N", "Y", r"Taken up by the practice as an instance of the work.")
E("CM3", "C", r"Datuna's eating of the banana", r"December 2019",
  r"Datuna described his eating of the banana as a performance, under a title of his own.",
  [], True, "maker", r"Datuna, at the fair and online", "curio", "none", True, "N", "Y",
  "0010010001", "Y", "N", "Y", r"Reported as an incident at the fair; our encoding.")
E("CM4", "C", r"Cattelan, \emph{Comedian}", r"Sotheby's, November 2024",
  r"An edition of the work was sold at Sotheby's in New York in 2024 for about \$6.2 million to the entrepreneur Justin Sun, who then ate the banana.",
  [], True, "other", r"Sotheby's", "mixed", "high", False, "N", "Y", "0010111001",
  "Y", "N", "Y", r"As in CM1; the sale adds market uptake only.")
E("BK1", "C", r"Banksy, \emph{Girl with Balloon}", r"Sotheby's London, 2018",
  r"Immediately after it was sold at auction in October 2018, the canvas passed partly through a shredder concealed in its frame. The artist renamed the result \emph{Love is in the Bin}; it was sold again at Sotheby's in 2021 for about eighteen and a half million pounds.",
  [], True, "maker", r"Banksy; Sotheby's", "mixed", "high", True, "N", "Y", "1110111011",
  "Y", "N", "Y", r"Engaged as a work and as a comment on the market.")

# ===================================================================== X
E("AI1", "X", r"\emph{Edmond de Belamy}", r"Christie's New York, October 2018",
  r"A print of a portrait generated with a generative adversarial network by the collective Obvious, signed with part of the algorithm's loss function. Christie's sold it for \$432{,}500 against an estimate of \$7{,}000 to \$10{,}000.",
  ["Hertzmann2018"], True, "other", r"Obvious; Christie's", "divided", "high", True, "N", "Y",
  "0000010001", "Y", "N", "Y", r"Discussed both as a work and as an event in the history of a technology.")
E("AI2", "X", r"\emph{Th\'e\^atre D'op\'era Spatial}", r"Colorado State Fair, 2022",
  r"An image produced by Jason M.~Allen with the text-to-image system Midjourney won first prize in the digital art category of the fine arts competition of the Colorado State Fair in 2022. The United States Copyright Office later refused to register it as a work of authorship.",
  [], True, "maker", r"Allen; Colorado State Fair", "divided", "none", True, "N", "Y",
  "1000010001", "Y", "N", "Y", r"A prize from a fair's judges, followed by a dispute over whether it should count as a work.")
E("AI3", "X", r"Anadol, \emph{Unsupervised}", r"Museum of Modern Art, 2022--2023",
  r"An installation by Refik Anadol displaying continuously generated imagery derived from a model trained on images of works in the Museum of Modern Art's collection, shown in the museum's lobby.",
  [], True, "maker", r"Anadol; Museum of Modern Art", "divided", "none", False, "?", "Y",
  "1000010011", "Y", "N", "Y", r"Reviewed both as a work and as spectacle or technology.")
E("AI4", "X", r"A generated image", r"schematic",
  r"An image produced by a generative model and stored on a server, seen by no one.",
  [], True, "no", None, "none", "none", False, "N", "N", "1000000000", "N", "N", "N",
  r"Not presented.", hyp=True)
E("AI5", "X", r"A generated image", r"schematic, offered and ignored",
  r"An image produced by a generative model and offered by its user to an online exhibition, where nobody comments on it.",
  [], True, "maker", r"its user, online", "none", "none", True, "N", "Y", "1000000001",
  "Y", "N", "Y", r"Presented; no engagement.", hyp=True)

# ===================================================================== S
E("SD1", "S", r"A declared breakfast", r"schematic",
  r"A participant in an artworld photographs her breakfast, declares it a work of art and posts it to her followers. No critic, curator or artist engages it.",
  [], True, "maker", r"the declarer, online", "none", "none", True, "N", "Y", "0000000001",
  "Y", "N", "Y", r"Presented; no engagement.", hyp=True)
E("SD2", "S", r"A curator's choice", r"schematic",
  r"The director of a major museum selects an ordinary object and exhibits it as a work. Critics, artists and historians ignore it.",
  [], True, "other", r"a museum director", "none", "none", True, "N", "Y", "0000000001",
  "Y", "N", "Y", r"Presented with institutional authority; no engagement.", hyp=True)
E("SD3", "S", r"A uniformly panned painting", r"schematic",
  r"A painting exhibited in a gallery and reviewed by several critics, all of whom find it worthless.",
  [], True, "maker", r"the painter, a gallery", "adverse", "none", False, "Y", "Y", "0000000111",
  "Y", "N", "Y", r"Engaged as a work and assessed unfavourably.", hyp=True)

# ===================================================================== additions
# D  objects mistaken, attacked or destroyed
E("HC1", "D", r"Hirst, installation at Eyestorm", r"London, October 2001",
  r"An installation by Damien Hirst made of studio debris, including coffee cups, ashtrays and beer bottles, was cleared away by a cleaner at the Eyestorm gallery, who took it for rubbish left over from a party. The gallery reassembled it.",
  [], True, "maker", r"Hirst; Eyestorm gallery", "mixed", "sold", False, "N", "Y",
  "0010111001", "Y", "N", "Y", r"Engaged as a work; the cleaner's act is one agent's failure to recognize it.")
E("MG1", "D", r"Metzger, auto-destructive art", r"Tate Britain, 2004",
  r"A bag of rubbish forming part of Gustav Metzger's recreation of his first public demonstration of auto-destructive art was thrown away by a cleaner at Tate Britain in 2004 and was replaced.",
  [], True, "maker", r"Metzger; Tate Britain", "favourable", "none", False, "N", "Y",
  "0010111001", "Y", "N", "Y", r"Engaged as a work; one agent's act of disposal.")
E("BF1", "D", r"Beuys, \emph{Fat Corner}", r"D\"usseldorf, 1986",
  r"A corner of fat installed by Joseph Beuys in a room of the Kunstakademie D\"usseldorf was removed by a caretaker cleaning the room in 1986, after the artist's death. Its owner, Beuys's former student Johannes St\"uttgen, sued the state of North Rhine-Westphalia for compensation, and in 1988 the Higher Regional Court in D\"usseldorf proposed a settlement of 40{,}000 marks.",
  [], True, "maker", r"Beuys; Kunstakademie D\"usseldorf", "favourable", "none", False, "N", "Y",
  "0110111001", "Y", "N", "Y", r"Engaged as a work; one agent's act of disposal.")
E("GB1", "D", r"Goldschmied \& Chiari, \emph{Where Shall We Go Dancing Tonight?}", r"Museion, Bolzano, 2015",
  r"An installation of empty bottles, confetti and cigarette ends at the Museion in Bolzano, alluding to the parties of the 1980s, was thrown away by cleaners in 2015 and restored from the refuse sacks.",
  [], True, "maker", r"the artists; Museion", "favourable", "none", False, "N", "Y",
  "0010111001", "Y", "N", "Y", r"Engaged as a work; the cleaners' act is not an act of the critical practice.")
E("YW1", "D", r"Umanets's inscription on a Rothko", r"Tate Modern, October 2012",
  r"Vladimir Umanets wrote his name and the words \enquote{a potential piece of yellowism} on Mark Rothko's \emph{Black on Maroon} at Tate Modern. He described the act as a contribution to a movement of his own devising and was sentenced to two years' imprisonment for criminal damage; the painting was restored.",
  [], True, "maker", r"Umanets, by inscription and statement", "curio", "none", True, "N", "Y",
  "0000010001", "Y", "N", "Y", r"Treated as vandalism and as news; our encoding.")
E("PN1", "D", r"Pinoncelli's attacks on \emph{Fountain}", r"N\^imes 1993; Paris 2006",
  r"Pierre Pinoncelli urinated into one of the replicas of \emph{Fountain} at an exhibition in N\^imes in 1993 and struck one with a hammer at the Centre Pompidou in 2006, presenting both acts as performances in the spirit of Dada.",
  [], True, "maker", r"Pinoncelli, by public statement", "curio", "none", True, "N", "Y",
  "0010010001", "Y", "N", "Y", r"Treated chiefly as attacks on a work and as news; our encoding.")
E("BC1", "D", r"Baldessari, \emph{Cremation Project}", r"1970",
  r"John Baldessari had the paintings he had made between 1953 and 1966 cremated and kept the ashes as a work, together with documentation of the cremation.",
  [], True, "maker", r"Baldessari; exhibitions", "favourable", "none", True, "N", "Y",
  "0010111001", "Y", "N", "Y", r"Engaged as a work in the history of conceptual art.")
E("ML1", "D", r"Landy, \emph{Break Down}", r"London, February 2001",
  r"In an empty department store on Oxford Street in London, Michael Landy and assistants catalogued and destroyed all 7{,}227 of his possessions over two weeks, in public.",
  [], True, "maker", r"Landy; Artangel", "mixed", "none", False, "N", "Y",
  "0110111001", "Y", "N", "Y", r"Engaged as a work, with divided assessments.")
E("AW1", "D", r"Ai Weiwei, \emph{Dropping a Han Dynasty Urn}", r"1995",
  r"A triptych of photographs showing the artist letting an urn said to be of the Han dynasty fall and break.",
  [], True, "maker", r"Ai Weiwei; exhibitions", "mixed", "sold", False, "N", "Y",
  "0110111011", "Y", "N", "Y", r"Engaged as a work, assessed for and against.")
E("BX1", "D", r"Brancusi, \emph{Bird in Space}", r"United States customs, 1926--1928",
  r"When a bronze \emph{Bird in Space} was imported into the United States in 1926 for exhibition, the customs authorities refused it the duty-free entry granted to works of art and assessed it as a manufactured metal object. In \emph{Brancusi v.\ United States} the Customs Court decided in 1928 that it was a work of art.",
  [], True, "maker", r"Brancusi; exhibition in New York", "favourable", "sold", False, "Y", "Y",
  "1010111111", "Y", "Y", "Y", r"Engaged as a work by critics and collectors; the customs classification and the ruling are not acts of the critical practice.")
E("SR1", "D", r"Serra, \emph{Tilted Arc}", r"Federal Plaza, New York, 1981--1989",
  r"A curved wall of steel installed in 1981 across Federal Plaza in Manhattan, commissioned by a federal programme for art in public buildings. After a public hearing in 1985 it was removed in 1989, over the artist's objection that the work was specific to its site.",
  [], True, "maker", r"Serra; the commissioning agency", "mixed", "sold", False, "N", "Y",
  "0010111111", "Y", "N", "Y", r"Engaged as a work and assessed with hostility and with praise.")

# further readymade, appropriation and instruction works
E("SL2", "M", r"Levine, \emph{Fountain (After Marcel Duchamp: A.P.)}", r"1991",
  r"A urinal cast in polished bronze by Sherrie Levine, exhibited under a title naming its source.",
  [], True, "maker", r"Levine; gallery exhibition", "mixed", "sold", True, "N", "Y",
  "1010111111", "Y", "N", "Y", r"Engaged as a work of its own, not as an instance of Duchamp's.")
E("LW1", "M", r"LeWitt, wall drawings", r"from 1968",
  r"Sol LeWitt's wall drawings exist as written instructions that are executed on a wall, often by assistants, and may be painted over and executed again elsewhere.",
  [], True, "maker", r"LeWitt; galleries and museums", "favourable", "sold", True, "N", "Y",
  "1011111011", "Y", "Y", "Y", r"Each execution taken up as an instance of the work.")
E("BR2", "M", r"Broodthaers, \emph{Mus\'ee d'Art Moderne, D\'epartement des Aigles}", r"Brussels, 1968",
  r"A fictional museum opened by Marcel Broodthaers in his house in Brussels in 1968, with packing cases, postcards and inscriptions, later extended through other sections and venues.",
  [], True, "maker", r"Broodthaers", "favourable", "none", True, "N", "Y",
  "0010111001", "Y", "Y", "Y", r"Engaged as a work, central to institutional critique.")
E("CB1", "P", r"Burden, \emph{Shoot}", r"Santa Ana, 1971",
  r"Chris Burden had an assistant shoot him in the arm with a rifle in a gallery in Santa Ana, California, before a small audience; the event is known through photographs and a short film.",
  [], True, "maker", r"Burden; F Space gallery", "mixed", "none", False, "N", "Y",
  "0110111001", "Y", "N", "Y", r"Engaged as a work of performance, assessed for and against.")

# further cases of neglect, rediscovery and posthumous presentation
E("VN1", "A", r"Van Gogh", r"1890",
  r"In January 1890 Albert Aurier published in the \emph{Mercure de France} an article praising Vincent van Gogh as an isolated visionary. In the same year van Gogh exhibited with Les XX in Brussels, where \emph{The Red Vineyard} was bought by the painter Anna Boch. He died in July 1890.",
  [], True, "maker", r"van Gogh; Les XX, Brussels; Salon des Ind\'ependants", "favourable", "sold", False, "Y", "Y",
  "1111111111", "Y", "Y", "Y", r"Engaged as works within the artist's lifetime, if narrowly.")
E("VR1", "O", r"Vermeer", r"revaluation from 1866",
  r"Vermeer's paintings were sold and collected in his lifetime and afterwards, but his reputation faded; in 1866 the critic Th\'eophile Thor\'e, writing as W.~B\"urger, published in the \emph{Gazette des Beaux-Arts} the articles that began his modern fame.",
  [], True, "other", r"Thor\'e-B\"urger; collectors and museums", "favourable", "high", False, "Y", "Y",
  "1111111111", "Y", "Y", "Y", r"Engaged as works both before and after the period of neglect.")
E("BM1", "O", r"Bach, \emph{St Matthew Passion}", r"Berlin, 1829",
  r"Composed for the Good Friday liturgy in Leipzig, the Passion was revived in a concert performance conducted by Felix Mendelssohn at the Berlin Singakademie in 1829, an event usually taken to begin the nineteenth-century revival of Bach's music.",
  [], True, "other", r"Mendelssohn; Berlin Singakademie", "favourable", "sold", False, "Y", "Y",
  "1111111111", "Y", "Y", "Y", r"Engaged as a work in concert life and criticism.")
E("KF1", "O", r"Kafka, \emph{The Trial}", r"publication, 1925",
  r"Franz Kafka asked his friend Max Brod to burn his unpublished manuscripts after his death. Brod did not comply and published the unfinished novel in 1925.",
  [], True, "other", r"Max Brod, against the author's instructions", "favourable", "sold", False, "?", "?",
  "1111111111", "?", "Y", "Y", r"Engaged as literature from its first publication.")
E("SE1", "O", r"S\'eraphine Louis", r"from 1912",
  r"S\'eraphine Louis, a housekeeper in Senlis who painted flowers and foliage, was discovered in 1912 by the German collector and critic Wilhelm Uhde, who bought and later exhibited her work.",
  [], True, "other", r"Wilhelm Uhde; exhibitions", "favourable", "sold", False, "Y", "?",
  "1111111110", "?", "Y", "Y", r"Engaged as works by a critic and, later, by museums.")
E("HR1", "A", r"Henri Rousseau", r"Salon des Ind\'ependants; 1908",
  r"Rousseau, a customs official who taught himself to paint, exhibited regularly at the Salon des Ind\'ependants, where his pictures were widely mocked. Picasso, who owned one of his portraits, gave a banquet in his honour in 1908.",
  [], True, "maker", r"Rousseau; Salon des Ind\'ependants", "mixed", "sold", False, "Y", "Y",
  "1111111011", "Y", "Y", "Y", r"Engaged as works, assessed with mockery and with admiration.")
E("VW1", "H", r"Venus of Willendorf", r"after 1908",
  r"A limestone figurine of a woman, found in 1908 near Willendorf in Austria and dated to more than twenty-five thousand years ago. It is held by the Natural History Museum in Vienna and figures in surveys of the history of art.",
  [], True, "other", r"archaeologists; surveys of the history of art", "favourable", "none", False, "?", "ur",
  "1101100110", "?", "Y", "?", r"Engaged as a work by art historians, although held by a museum of natural history.")
E("KN1", "F", r"Knoedler forgeries", r"to 2011",
  r"For some fifteen years the New York gallery Knoedler \& Company sold paintings attributed to Rothko, Pollock, Motherwell and other Abstract Expressionists, supplied by a dealer and painted by a painter in Queens. The gallery closed in 2011 amid the resulting lawsuits.",
  [], True, "other", r"Knoedler \& Company", "favourable", "high", False, "Y", "Y",
  "1100001111", "Y", "N", "Y", r"Engaged as works by experts and collectors, under false attributions.")
