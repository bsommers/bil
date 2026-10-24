# Citations — `bil` white paper and domain models

Every source cited by the white paper and by `examples/domains/*.bil` is listed here once, under a
stable key such as `[roth1990]`. The models and the paper cite these keys inline, together with the link.

Research date: 2026-10-23.

## How sources were qualified

| Tier | Kind of source | How it is used |
|---|---|---|
| **A** | Normative standard, protocol specification, regulator or government investigator (ISO, IEC, OASIS, NIST, FDA, CSB, FHWA, NAMUR) | Requirements and limits that the models encode |
| **B** | Peer-reviewed paper, scholarly book, or government research lab report | Physics, algorithms, prior verification work |
| **C** | Manufacturer documentation, datasheets, patents | Engineering practice and failure modes |
| **D** | Secondary sources: training sites, simulator guides, wikis, blogs | Corroboration only, and always marked as such |

The **Verified** column records how much of each source was actually read:

- **text**: the cited passage was read in the primary document.
- **abstract**: only the abstract or a catalog record was read.
- **secondary**: the figure comes from sources that quote a paywalled standard. The standard itself was not
  read, so check it before relying on the figure.

Numbers that appear in a model (such as 250 mm/s or 0.5 s) are illustrative parameters taken from these
sources. They are **not** compliance claims. A real design must take its parameters from the current
edition of the governing standard.

---

## Foundations: formal methods and tools

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[dijkstra1975]` | B | E. W. Dijkstra, "Guarded commands, nondeterminacy and formal derivation of programs," *CACM* 18(8):453–457, 1975. https://doi.org/10.1145/360933.360975 · EWD 472 transcription: https://www.cs.utexas.edu/users/EWD/transcriptions/EWD04xx/EWD472.html | abstract | GCL `if … fi` / `do … od`, weakest preconditions, nondeterminism |
| `[newcombe2015]` | B | C. Newcombe, T. Rath, F. Zhang, B. Munteanu, M. Brooker, M. Deardeuff, "How Amazon Web Services Uses Formal Methods," *CACM* 58(4), 2015. https://doi.org/10.1145/2699417 · https://cacm.acm.org/magazines/2015/4/184701-how-amazon-web-services-uses-formal-methods/fulltext | abstract | Industrial precedent: model checking designs before they ship |
| `[lattuada2023]` | B | A. Lattuada et al., "Verus: Verifying Rust Programs using Linear Ghost Types," *Proc. ACM Program. Lang.* 7(OOPSLA1), art. 85, 2023. https://doi.org/10.1145/3586037 | abstract | `spec` / `proof` / `exec` modes, `bil emit-verus` target |
| `[demoura2008]` | B | L. de Moura, N. Bjørner, "Z3: An Efficient SMT Solver," TACAS 2008, LNCS 4963. https://doi.org/10.1007/978-3-540-78800-3_24 | abstract | The SMT back end that discharges the obligations |
| `[holzmann1997]` | B | G. J. Holzmann, "The Model Checker SPIN," *IEEE TSE* 23(5):279–295, 1997. https://doi.org/10.1109/32.588521 | abstract | Explicit-state, interleaving-semantics model checking |
| `[peterson1981]` | B | G. L. Peterson, "Myths about the mutual exclusion problem," *Inf. Process. Lett.* 12(3):115–116, 1981. https://doi.org/10.1016/0020-0190(81)90106-X | abstract | `examples/mutex_protocol.bil` |

## Semiconductor manufacturing: spectroscopic ellipsometry and solid-phase epitaxy

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[roth1990]` | B | J. A. Roth, G. L. Olson, D. C. Jacobson, J. M. Poate, *Appl. Phys. Lett.* 57, 1340 (1990). Values as quoted in `[johnson2007]`. | text (via `[johnson2007]`) | Intrinsic Si SPE: v₀ = 4.64×10¹⁶ Å/s, Eₐ = 2.7 eV, which gives the `spe_rate` table |
| `[johnson2007]` | B | B. C. Johnson, J. C. McCallum, "Dopant-enhanced solid phase epitaxy in buried amorphous silicon layers," *Phys. Rev. B* 76, 045216 (2007). https://doi.org/10.1103/PhysRevB.76.045216 · arXiv: https://arxiv.org/abs/1007.5372 | text | Fit v₀ = (4±1)×10¹⁶ Å/s, Eₐ = 2.68±0.04 eV; time-resolved reflectivity; 460–660 °C anneals |
| `[olsonroth1988]` | B | G. L. Olson, J. A. Roth, "Kinetics of solid phase crystallization in amorphous silicon," *Mater. Sci. Rep.* 3, 1 (1988). https://www.sciencedirect.com/science/article/pii/S0920230788800057 | secondary (search excerpt) | SPE Eₐ ≈ 2.7 eV over about 470–1350 °C; random nucleation Eₐ ≈ 4 eV, so nucleation gains on SPE as temperature rises, which motivates the upper limit of the window |
| `[olson1985]` | B | G. L. Olson, "Kinetics and Mechanisms of Solid Phase Epitaxy and Competitive Processes in Silicon," *MRS Proc.* 35, 25 (1985). https://doi.org/10.1557/PROC-35-25 | abstract | Kinetic competition between SPE and random crystallization |
| `[thompson1984]` | B | M. O. Thompson et al., "Melting temperature and explosive crystallization of amorphous silicon during pulsed laser irradiation," *Phys. Rev. Lett.* 52, 2360 (1984). https://link.aps.org/doi/10.1103/PhysRevLett.52.2360 · abstract: https://impact.ornl.gov/en/publications/melting-temperature-and-explosive-crystallization-of-amorphous-si/ | abstract | a-Si melts 200±50 K below c-Si; a self-propagating liquid layer at 10–20 m/s leaves fine-grained poly-Si. This is the `NeverMeltAmorphousSi` hazard |
| `[lohner1996]` | B | "Spectro-ellipsometric Studies of Amorphization and Thermal Annealing in Ion-implanted Silicon," *Jpn. J. Appl. Phys.* 35, 5929 (1996). https://doi.org/10.1143/JJAP.35.5929 · group's methods: https://ris.utwente.nl/ws/files/6689010/Lohner93ion.pdf | abstract | SE with multilayer optical models gives damaged/amorphous layer thickness. Caveat: low damage can be overestimated with unsuitable dielectric functions, which motivates the `mse_milli` gate |
| `[holgado1995]` | B | S. Holgado, J. Martinez, J. Garrido, J. Piqueras, "Regrowth-process study of amorphous BF₂⁺ ion-implanted silicon layers through spectroscopic ellipsometry," *Appl. Phys. A* 60(3), 325–332 (1995). https://doi.org/10.1007/BF01538413 | abstract | SE applied to the regrowth of implant-amorphized Si |
| `[fujiwara1998]` | B | H. Fujiwara, J. Koh, Y. Lee, C. R. Wronski, R. W. Collins, "Real Time Spectroscopic Ellipsometry Studies of the Solid Phase Crystallization of Amorphous Silicon," *MRS Proc.* 507, 939 (1998). https://doi.org/10.1557/PROC-507-939 | abstract | Real-time SE gives near-surface temperature calibration and crystalline volume fraction during anneal, which is the in-situ endpoint in `SpeAnneal` |
| `[fujiwara2007]` | B | H. Fujiwara, *Spectroscopic Ellipsometry: Principles and Applications*, Wiley, 2007, ISBN 978-0-470-01608-4. Excerpt: https://catalogimages.wiley.com/images/db/pdf/9780470016084.excerpt.pdf | abstract | Ψ/Δ as the measured amplitude ratio and phase difference; real-time monitoring and process control |
| `[norman1991]` | B | S. A. Norman, C. D. Schaper, S. P. Boyd, "Improvement of Temperature Uniformity in Rapid Thermal Processing Systems Using Multivariable Control," 1991. https://web.stanford.edu/~boyd/papers/temperature_uniformity.html | abstract | Non-uniformity during ramps causes slip, which limits the ramp rate. This is the slew limit in `thermal_setpoint` |
| `[uspto6403925]` | C | US Patent 6,403,925, "System and method for thermal processing of a semiconductor substrate." https://image-ppubs.uspto.gov/dirsearch-public/print/downloadPdf/6403925 | abstract | Edge-cool gradients above ~800 °C produce slip lines |
| `[uspto6034356]` | C | US Patent 6,034,356, "RTP lamp design for oxidation and annealing." https://image-ppubs.uspto.gov/dirsearch-public/print/downloadPdf/6034356 | secondary | Typical RTP ramp rates 20–100 °C/s versus 5–10 °C/min in furnaces |

## Collaborative robotics

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[marvel2017]` | B | J. A. Marvel, R. Norcross, "Implementing speed and separation monitoring in collaborative robot workcells," *Robotics and Computer-Integrated Manufacturing* (NIST). https://doi.org/10.1016/j.rcim.2016.08.001 · https://www.nist.gov/node/1097971 | abstract | ISO/TS 15066 SSM protective separation distance and how to implement it |
| `[szabo2012]` | B | S. Szabo, W. Shackleford, R. Norcross, J. Marvel, NIST IR 7851 (2012). https://nvlpubs.nist.gov/nistpubs/ir/2012/NIST.IR.7851.pdf | abstract | Laser-scanner SSM testbed that issues stop/restart from the separation distance |
| `[isots15066]` | A | ISO/TS 15066, Robots and robotic devices — Collaborative robots. Overview: https://www.automate.org/tech-papers/iso-ts-15066-explained | secondary | SSM as one of the four collaborative modes; supplements ISO 10218-1/-2 |
| `[iso10218]` | A | ISO 10218-1/-2, reduced speed of 250 mm/s. Quoted by https://www.controldesign.com/safety/functional-safety/article/55300304/how-to-understand-safe-reduced-speed-and-safe-limited-speed and https://manual.doosanrobotics.com/en/user-manual/3.2.1/2-a-series/manual-mode | secondary | The 250 mm/s reduced-speed cap used in `ssm_speed_limit` |

## Control systems

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[scilab_aw]` | D | "PID Anti-Windup Schemes," Scilab. https://scilab.org/pid-anti-windup-schemes | text | Conditional integration and back-calculation are the two basic anti-windup schemes (`integrate` uses conditional integration) |
| `[astrom_murray]` | B | K. J. Åström, R. M. Murray, *Feedback Systems*, Princeton University Press (PID chapter, integrator windup). Course copy cited by MathWorks: http://www.cds.caltech.edu/~murray/courses/cds101/fa02/caltech/astrom-ch6.pdf | secondary | Standard reference for windup |

## Navigation and autonomy

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[nasa_safeguard]` | B | NASA Langley, Safeguard geofencing: https://technology.nasa.gov/patent/LAR-TOPS-244 · NTRS report: https://ntrs.nasa.gov/api/citations/20190000716/downloads/20190000716.pdf · geofence algorithms proved in PVS: https://ntrs.nasa.gov/api/citations/20170009617/downloads/20170009617.pdf | abstract | Precedent for formally verified stay-in/stay-out geofencing that runs independently of the autopilot |

## Industrial IoT

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[mqtt311]` | A | OASIS, *MQTT Version 3.1.1*, OASIS Standard, 29 Oct 2014. https://docs.oasis-open.org/mqtt/mqtt/v3.1.1/os/mqtt-v3.1.1-os.html | text | §4.2: "requires an underlying transport that provides an ordered, lossless, stream of bytes"; §4.3.3 [MQTT-4.3.3-2]: until PUBREL the receiver acknowledges re-sent PUBLISHes and "MUST NOT cause duplicate messages to be delivered"; §4.6 [MQTT-4.6.0-1] re-send in original order |
| `[emqx_qos]` | D | EMQX, "Introduction to MQTT QoS." https://emqx.io/blog/introduction-to-mqtt-qos | abstract | Sender-side QoS 2 flow |
| `[namur_ne43]` | A | NAMUR NE 43 (ed. 2021-07-26), standardization of the failure signal level of digital transmitters. https://www.namur.net/en/publications/news-archive/ne-43-has-been-revised.html | secondary | 3.8–20.5 mA measurement band; ≤ 3.6 mA or ≥ 21 mA signals a failure. Bands quoted by https://www.microcontrol.net/en/service/measurement-technology/industrial-standard-signals/ and https://www.electricalvolt.com/what-is-namur-ne-43 |

## Manufacturing machinery

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[iso13851]` | A | ISO 13851:2019, Two-hand control devices. https://committee.iso.org/standard/35560.html | secondary | Type III: both actuators within 0.5 s, release before re-triggering. Quoted by Eaton (https://origin.golfpride.com/gb/en-gb/markets/machine-building/service-and-support-machine-building-moem-service-eaton/blogs/Two-hand-control-for-machinery-blog-functional-safety.html) and by Phoenix Contact's type IIIA relay, "synchronous activation monitoring < 0.5 s" (https://www.phoenixcontact.com/us/products/2700571/pdf, tier C) |
| `[iso13855]` | A | ISO 13855, positioning of protective equipment: S = K·T + C, K = 2000 mm/s, C = 8(d − 14) for d ≤ 40 mm. Quoted by https://www.issa.int/sites/default/files/documents/prevention/2Light_Curtain_2011_en-36159.pdf and https://www.leuze.com/en-us/navigation/0942f478ebd948d9b0b7c4c7734c3714 | secondary | `light_curtain_distance`. **Sources disagree** on the K = 1600 / 500 mm switch-over between editions, so the model always uses K = 2000 (the larger distance) |

## Critical process systems

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[csb_t2]` | A | U.S. Chemical Safety Board, T2 Laboratories explosion (2009). https://www.csb.gov/csb-finds-t2-laboratories-explosion-caused-by-failure-of-cooling-system-resulting-in-runaway-chemical-reaction-report-notes-company-did-not-recognize-hazards-of-chemical-process/ | abstract | Cooling failure leading to runaway reaction (4 killed, 28 injured nearby). This is the `ReactorSis` scenario |
| `[lundteigen_sis]` | B | M. A. Lundteigen, M. Rausand, SIS book ch. 12, "Spurious trip rate," NTNU. https://ntnu.edu/documents/624876/1277046207/SIS+book+-+chapter+12+-+Spurious+trip+rate/ad91f310-f8b2-41f5-a923-3e9e22971f75 | abstract | 2oo3 tolerates one fault both against failure to trip and against spurious trips; the two `high_temp_trip` properties |
| `[iec61511]` | A | IEC 61511, Functional safety — SIS for the process industry sector. Hardware fault tolerance by SIL (IEC 61511-1:2018 §11.4), as summarized by https://open-exam-prep.com/study-guides/pe-control-systems/sis-design-sil/sis-design-constraints | secondary | Voting architectures and HFT |
| `[kenexis_2oo3]` | C | Kenexis, "Comparison of 2oo3 voting and 2oo2 voting." https://kenexis.com/wp-content/uploads/2018/11/Comparison-of-2oo3-voting-and-2oo2-voting.pdf | abstract | Cost and complexity trade-offs of 2oo3 |

## Surgical robotics

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[rosenberg1993]` | B | L. B. Rosenberg, "Virtual fixtures as tools to enhance operator performance in telepresence environments," *Proc. SPIE* 2057 (1993). https://doi.org/10.1117/12.164901 | abstract | Origin of virtual fixtures |
| `[abbott2007]` | B | J. J. Abbott, P. Marayong, A. M. Okamura, "Haptic Virtual Fixtures for Robot-Assisted Manipulation," *Robotics Research*, Springer, 2007. https://doi.org/10.1007/978-3-540-48113-3_5 · PDF: https://my.eng.utah.edu/~jabbott/pmwiki/uploads/Main/Abbott_RoboticsResearch07.pdf | abstract | Forbidden-region virtual fixtures keep the manipulator out of forbidden regions (`fixture_step`); da Vinci and the JHU Steady-Hand robot |
| `[iec80601277]` | A | IEC 80601-2-77:2019+AMD1:2023, robotically assisted surgical equipment (RASE). https://www.iso.org/standard/68473.html | abstract | Basic safety and essential performance of RASE/RASS |

## Medical devices (infusion pumps)

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[fda_ipii]` | A | U.S. FDA, *White Paper: Infusion Pump Improvement Initiative*, April 2010. https://www.fda.gov/medical-devices/infusion-pumps/white-paper-infusion-pump-improvement-initiative · PDF: https://www.fda.gov/media/116949/download | abstract | ~56,000 adverse-event reports (2005–2009), 87 recalls (14 Class I); software defects including failures of built-in safety alarms; problems traced to design and engineering |
| `[kim2011gpca]` | B | B. Kim et al., "Safety-Assured Development of the GPCA Infusion Pump Software," UPenn. https://repository.upenn.edu/cis_papers/475 | abstract | FDA Generic PCA reference model checked in UPPAAL against FDA's generic safety requirements |
| `[gpca_umn]` | B | University of Minnesota CRISYS, GPCA requirements and artifacts. https://crisys.cs.umn.edu/gpca.shtml | abstract | Home of the GPCA requirements documents |

## Public safety

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[mutcd4d26]` | A | FHWA *MUTCD* (2009) §4D.26, Yellow Change and Red Clearance Intervals. Quoted by the NJDOT technical appendix (https://dot.nj.gov/transportation/about/publicat/lmreports/pdf/2013rlrtechnicalappendix.pdf) and a state reprint (https://regulations.justia.com/states/delaware/title-2/2000/2400/2402/part-4/chapter-4d/section-4d-26) | secondary | A steady yellow follows every green; yellow should last 3–6 s; red clearance is set by engineering practice. This is the `Yellow` phase that every green passes through |
| `[mmu]` | D | Conflict Monitor Units and Malfunction Management Units (NEMA TS-1/TS-2). https://open-exam-prep.com/study-guides/imsa-traffic-signal-i/cabinet-wiring-and-components/cmu-and-mmu | abstract | Hardware monitor that forces flash on conflicting greens. `NoConflictingGreens` is the same property, proved at design time |
| `[heitmeyer1994]` | B | C. Heitmeyer, N. Lynch, "The Generalized Railroad Crossing: A Case Study in Formal Verification of Real-Time Systems," MIT LCS TM-511 / IEEE RTSS 1994. https://groups.csail.mit.edu/tds/papers/Heitmeyer/TM-511.html · benchmark: https://groups.csail.mit.edu/tds/grc.html | abstract | Safety (gate down whenever the crossing is occupied) and utility (gate up otherwise). This is the `LevelCrossing` model |

## Cybersecurity

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[nist80063b]` | A | NIST SP 800-63B, Digital Identity Guidelines: Authentication, §3.2.2 Rate Limiting (Throttling). https://pages.nist.gov/800-63-4/sp800-63b.html | text | No more than 100 consecutive failures per authenticator (then disable it); agencies may set lower limits. The model's 5 is such a lower limit |
| `[beurdouche2015]` | B | B. Beurdouche et al., "A Messy State of the Union: Taming the Composite State Machines of TLS," IEEE S&P 2015, pp. 535–552; *CACM* reprint https://doi.org/10.1145/3023357 · https://hal.archives-ouvertes.fr/hal-01114250 | abstract | State-machine bugs (SKIP, FREAK) let an attacker skip messages. This is the `ClientHandshake` seeded bug |
| `[ncc_smack]` | C | NCC Group, "SMACK: SKIP-TLS & FREAK SSL/TLS vulnerabilities." https://www.nccgroup.com/research/smack-skip-tls-freak-ssltls-vulnerabilities/ | abstract | CVE-2014-6593 (SKIP-TLS), CVE-2015-0204 (FREAK) |
| `[rfc2697]` | A | J. Heinanen, R. Guerin, RFC 2697, *A Single Rate Three Color Marker*, 1999. https://www.rfc-editor.org/rfc/rfc2697 | text | Token buckets that start full and fill at a committed rate, capped at the burst size (`refill`, `spend`) |
| `[nist80053ac5]` | A | NIST SP 800-53 Rev. 5, AC-5 Separation of Duties. Catalog summary: https://www.upguard.com/compliance/nist-sp-800-53/ac/ac-5 | abstract | `SeparationOfDuties` axiom |

## Automotive

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[iso15622]` | A | ISO 15622, Adaptive cruise control systems. https://www.iso.org/standard/89465.html | abstract | ACC control strategy, minimum functionality, driver interface, failure reaction |
| `[bernsteiner2016]` | B | S. Bernsteiner, *Integration of Advanced Driver Assistance Systems on Full-Vehicle Level*, TU Graz, 2016, ch. 6, p. 78. https://austria-forum.org/web-books/driverassistance00en2017isds/000100 | text | Minimum selectable time gap of 1 s in one standard and 0.8 s in another; Fancher et al. recommend 1–2 s. The model's 1.5 s lies in that range |

## Battery systems

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[uspto11592485]` | C | US 11,592,485 B2, "Methods and apparatus for contactor weld detection in a vehicle." https://patents.google.com/patent/US11592485 | abstract | Welded main contactor detected when the load-side voltage does not decay after an open command |
| `[uspto12077054]` | C | US 12,077,054 B2, "Vehicle main contactor weld detection system." https://patents.google.com/patent/US12077054 | abstract | Inrush-based weld detection and response |
| `[uspto10476262]` | C | US 10,476,262, "Dual-bus battery precharge circuit." https://image-ppubs.uspto.gov/dirsearch-public/print/downloadPdf/10476262 | abstract | Precharge before main contactor closure; welds come from inrush above making capacity (`ClosedOnlyAfterPrecharge`) |

## Aerospace

| Key | Tier | Source | Verified | Supports |
|---|---|---|---|---|
| `[airbus_laws]` | D | Airbus normal-law protections, as summarized from Airbus FCTM material by Code7700: https://code7700.com/airbus_control_laws.htm · FlyByWire A32NX (simulator) guide: https://docs.flybywiresim.com/pilots-corner/a32nx/a32nx-advanced-guides/protections/overview/ · https://en.wikipedia.org/wiki/Flight_control_modes | secondary | Bank beyond 33° needs continuous sidestick input, release returns to 33°, 67° limit; between α-prot and α-max the stick commands AoA, α-max is never exceeded; α-prot disengages the autopilot. **Illustrative only: verify against the type's FCOM** |
