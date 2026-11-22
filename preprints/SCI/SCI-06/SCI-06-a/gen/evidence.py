"""Evidential claims on which the favourable outcomes of Table 'crit' rest.

Each entry: (id, claim as a speaker of T1 could state it, term readings of the
manual of that revolution used in stating it, criteria it bears on).
Check C9 (in generate.py): every criterion recorded as favouring the successor
is supported by at least one claim, and every claim is stated with term
readings that all have referents in T2, so that both communities could state
and assess it.
"""

EVID = {
    'CHEM': [
        ('E1', 'Tin calcined in a sealed retort gains weight only when the retort is opened and air rushes in, by the weight of the air admitted (Lavoisier, 1774).', ['CH09', 'CH07', 'CH06', 'CH11'], ['accuracy']),
        ('E2', 'The red calx of mercury heated alone gives back the metal and an air that supports a flame better than common air (Priestley; Lavoisier).', ['CH06', 'CH07', 'CH02a', 'CH08', 'CH11'], ['accuracy', 'fruitfulness']),
        ('E3', 'Inflammable air exploded with dephlogisticated air leaves water, nearly the whole of both airs being consumed (Cavendish, 1784).', ['CH04a', 'CH02c', 'CH21'], ['accuracy', 'fruitfulness']),
        ('E4', 'Water passed over red-hot iron yields inflammable air, and the iron becomes a calx heavier than the metal (Lavoisier and Meusnier, 1784).', ['CH21', 'CH04a', 'CH06', 'CH07'], ['accuracy']),
    ],
    'ASTR': [
        ('E1', 'Mars\'s positions observed by Tycho Brahe are fitted by Kepler\'s ellipse to within the errors of observation, after the best circular model failed by about 8 minutes of arc.', ['AS01a', 'AS13'], ['accuracy', 'simplicity']),
        ('E2', 'The transit of Mercury of 1631 occurred close to the time predicted from the Rudolphine Tables (Gassendi).', ['AS01d', 'AS13'], ['accuracy']),
        ('E3', 'The ratio of epicycle to deferent radius for each planet yields, on the Copernican arrangement, the relative distances of the planets.', ['AS06a', 'AS05a', 'AS06b', 'AS05b', 'AS22'], ['scope']),
        ('E4', 'Superior planets retrograde only at opposition and inferior planets only near inferior conjunction.', ['AS11', 'AS01a', 'AS01d', 'AS13'], ['scope']),
        ('E5', 'Kepler\'s third law relates the periods and the mean distances of all the planets.', ['AS21a', 'AS22'], ['fruitfulness', 'simplicity']),
    ],
    'MECH': [
        ('E1', 'The perihelion of Mercury advances by about 43 seconds of arc per century more than the perturbations of the other planets account for (Le Verrier; Newcomb).', ['ME13', 'ME11'], ['accuracy']),
        ('E2', 'Starlight passing near the Sun is deflected (eclipse expeditions of 1919).', ['ME15', 'ME11'], ['accuracy']),
        ('E3', 'No effect of the Earth\'s motion on the round-trip time of light in perpendicular arms is detected (Michelson and Morley, 1887).', ['ME15', 'ME05'], ['consistency', 'scope']),
        ('E4', 'The mass of fast cathode-ray electrons, measured by deflection, increases with velocity (Kaufmann; Bucherer, 1908).', ['ME01', 'ME05'], ['scope', 'fruitfulness']),
    ],
    'HEAT': [
        ('E1', 'Boring a cannon with a blunt tool heats the metal and its water bath without limit while the boring continues (Rumford, 1798).', ['HE15', 'HE02'], ['accuracy']),
        ('E2', 'A fixed quantity of work spent in friction or in stirring water produces a fixed quantity of heat (Joule, 1840s).', ['HE15', 'HE02', 'HE03'], ['accuracy', 'fruitfulness']),
        ('E3', 'The viscosity of a gas is independent of its density over a wide range (Maxwell, 1866).', ['HE18', 'HE19'], ['scope']),
        ('E4', 'Air heats on compression and cools on expansion, and the speed of sound requires the ratio of specific heats.', ['HE10', 'HE11', 'HE12'], ['scope']),
    ],
    'QUAN': [
        ('E1', 'The spectral density of cavity radiation falls at high frequency, contrary to the Rayleigh--Jeans law (Lummer and Pringsheim; Rubens and Kurlbaum, 1899--1900).', ['QU13', 'QU12'], ['accuracy']),
        ('E2', 'The atomic heats of diamond and other solids fall far below the Dulong--Petit value at low temperatures (Weber; Nernst).', ['QU14', 'QU12'], ['accuracy', 'scope']),
        ('E3', 'The maximum energy of photoelectrons depends on the frequency of the light, not on its intensity (Lenard, 1902; Millikan, 1916).', ['QU15', 'QU09', 'QU05'], ['accuracy', 'fruitfulness']),
        ('E4', 'Atoms are stable and emit sharp spectral lines.', ['QU07', 'QU11'], ['consistency', 'scope']),
        ('E5', 'A beam of silver atoms is split into two discrete beams by an inhomogeneous magnetic field (Stern and Gerlach, 1922).', ['QU17', 'QU16'], ['accuracy']),
    ],
    'BIOL': [
        ('E1', 'The species of the Galapagos are allied to those of the nearest mainland, South America, and differ from island to island.', ['BI01', 'BI10b'], ['scope']),
        ('E2', 'Homologous bones underlie the forelimbs of man, bat and porpoise.', ['BI07'], ['scope', 'simplicity']),
        ('E3', 'Rudimentary teeth occur in foetal whales and are absorbed before birth.', ['BI11'], ['scope']),
        ('E4', 'Extinct edentates of South America are allied to the living armadillos and sloths of the same continent.', ['BI14', 'BI01'], ['scope', 'fruitfulness']),
        ('E5', 'Domestic breeds descended from one wild species differ more than many wild species do (pigeons).', ['BI17', 'BI01', 'BI23'], ['simplicity']),
    ],
    'PHYS': [
        ('E1', 'The left ventricle holds a measurable quantity of blood, and the heart beats over a thousand times in half an hour (De motu cordis, ch.~9).', ['GA07', 'GA12'], ['accuracy']),
        ('E2', 'A ligature tight enough to stop the arteries makes the hand pale and cold; loosened enough to let the arteries pass, it makes the veins below it swell (De motu cordis, ch.~11).', ['GA13', 'GA02', 'GA01'], ['accuracy']),
        ('E3', 'Blood pressed in a vein of the arm moves readily toward the heart and cannot be pushed past the valves away from it (De motu cordis, ch.~13).', ['GA17', 'GA01'], ['accuracy', 'fruitfulness']),
        ('E4', 'No pores can be found in the interventricular septum on dissection.', ['GA07'], ['consistency']),
        ('E5', 'Under the microscope blood is seen passing from arteries to veins in the lung of the frog (Malpighi, 1661).', ['GA22', 'GA02', 'GA01'], ['fruitfulness']),
    ],
    'OPTI': [
        ('E1', 'A bright spot appears at the centre of the shadow of a small opaque disk (Arago, 1819).', ['OP16', 'OP07'], ['accuracy']),
        ('E2', 'The positions of the fringes outside the shadow of an edge vary with distance as Fresnel\'s integrals predict.', ['OP07', 'OP16'], ['accuracy', 'scope']),
        ('E3', 'Two beams polarized at right angles do not form fringes when recombined (Fresnel and Arago, 1819).', ['OP09'], ['scope']),
        ('E4', 'Light travels more slowly in water than in air (Foucault, 1850).', ['OP06'], ['accuracy', 'fruitfulness']),
    ],
    'MIAS': [
        ('E1', 'Broth boiled in a swan-necked flask stays unchanged until the neck is broken (Pasteur, 1859--1862).', ['MI06'], ['scope']),
        ('E2', 'The blood of animals dead of anthrax contains rod-shaped bodies, cultures of which reproduce the disease (Koch, 1876).', ['MI18', 'MI05b'], ['accuracy']),
        ('E3', 'Cholera deaths in 1854 clustered about the Broad Street pump; customers of the Southwark and Vauxhall Company died at a far higher rate than those of the Lambeth Company (Snow, 1855).', ['MI21', 'MI13a'], ['accuracy']),
        ('E4', 'Compound fractures dressed with carbolic acid rarely suppurated (Lister, 1867).', ['MI16', 'MI14'], ['fruitfulness']),
        ('E5', 'Sheep vaccinated with attenuated anthrax cultures survived inoculation that killed unvaccinated sheep (Pouilly-le-Fort, 1881).', ['MI15', 'MI05b'], ['fruitfulness']),
    ],
    'HERE': [
        ('E1', 'In the second generation from crosses of true-breeding peas, the dominant and recessive forms appear in the ratio of about 3:1.', ['HR07', 'HR08', 'HR11', 'HR03'], ['accuracy']),
        ('E2', 'Characters absent in the first-generation hybrids reappear unchanged in the second.', ['HR08', 'HR16', 'HR11'], ['accuracy', 'scope']),
        ('E3', 'Selection within a pure line of beans does not shift the mean seed size of its progeny (Johannsen, 1903).', ['HR07', 'HR10'], ['scope']),
        ('E4', 'In Drosophila the white-eye character is transmitted with sex (Morgan, 1910).', ['HR11', 'HR16'], ['scope', 'fruitfulness']),
    ],
}
