include "cuni.mm"
include "wrel.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "wi.mm"
include "wal.mm"
include "wfun.mm"
include "wral.mm"
include "cres.mm"
include "bnj1095.mm"
include "nf5i.mm"
include "nfra1.mm"
include "nfan.mm"
include "nfxfr.mm"
include "bnj946.mm"
include "biimpi.mm"
include "19.21bi.mm"
include "bnj832.mm"
include "funrel.mm"
include "syl6.mm"
include "ralrimi.mm"
include "reluni.mm"
include "sylibr.mm"
include "w3a.mm"
include "wex.mm"
include "wrex.mm"
include "eluni2.mm"
include "bnj1196.mm"
include "bnj836.mm"
include "nfv.mm"
include "nf3an.mm"
include "nf5ri.mm"
include "bnj1345.mm"
include "simp3bi.mm"
include "bnj835.mm"
include "syl.mm"
include "nfra2.mm"
include "cfv.mm"
include "simprbi.mm"
include "bnj1219.mm"
include "bnj1294.mm"
include "simp2bi.mm"
include "fveq1d.mm"
include "cdm.mm"
include "cin.mm"
include "vex.mm"
include "opeldm.mm"
include "bnj837.mm"
include "elind.mm"
include "syl6eleqr.mm"
include "fvres.mm"
include "3eqtr3d.mm"
include "funopfv.mm"
include "sylc.mm"
include "funeq.mm"
include "cbvralv.mm"
include "sylib.mm"
include "bnj593.mm"
include "bnj937.mm"
include "sylbir.mm"
include "3expib.mm"
include "alrimivv.mm"
include "alrimiv.mm"
include "dffun4.mm"
include "sylanbrc.mm"

theorem bnj1379
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cD: class D
  let vf: setvar f
  let vg: setvar g
  assume bnj1379.1: |- ( ph <-> A. f e. A Fun f )
  assume bnj1379.2: |- D = ( dom f i^i dom g )
  assume bnj1379.3: |- ( ps <-> ( ph /\ A. f e. A A. g e. A ( f |` D ) = ( g |` D ) ) )
  assume bnj1379.5: |- ( ch <-> ( ps /\ <. x , y >. e. U. A /\ <. x , z >. e. U. A ) )
  assume bnj1379.6: |- ( th <-> ( ch /\ f e. A /\ <. x , y >. e. f ) )
  assume bnj1379.7: |- ( ta <-> ( th /\ g e. A /\ <. x , z >. e. g ) )

  disjoint A f
  disjoint A g
  disjoint A x
  disjoint A y
  disjoint A z
  disjoint f g
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint D x
  disjoint g ph
  disjoint ps x
  disjoint ps y
  disjoint ps z
  assert |- ( ps -> Fun U. A )

  proof
    wps
    cA
    cuni
    #
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @0
    wcel
    #
    @2
    vz
    cv
    #
    cop
    #
    @0
    wcel
    #
    wa
    @3
    @6
    wceq
    #
    wi
    #
    vz
    wal
    vy
    wal
    #
    vx
    wal
    @0
    wfun
    wps
    vf
    cv
    #
    wrel
    #
    vf
    cA
    wral
    @1
    wps
    @13
    vf
    cA
    wps
    wph
    @12
    cD
    cres
    #
    vg
    cv
    #
    cD
    cres
    #
    wceq
    #
    vg
    cA
    wral
    #
    vf
    cA
    wral
    #
    wa
    #
    vf
    bnj1379.3
    wph
    @19
    vf
    wph
    vf
    wph
    @12
    wfun
    #
    vf
    cA
    bnj1379.1
    bnj1095
    nf5i
    @18
    vf
    cA
    nfra1
    nfan
    nfxfr
    #
    wps
    @12
    cA
    wcel
    #
    @21
    @13
    wph
    @19
    @23
    @21
    wi
    #
    wps
    bnj1379.3
    wph
    @24
    vf
    wph
    @24
    vf
    wal
    wph
    @21
    vf
    cA
    bnj1379.1
    bnj946
    biimpi
    19.21bi
    bnj832
    @12
    funrel
    syl6
    ralrimi
    vf
    cA
    reluni
    sylibr
    wps
    @11
    vx
    wps
    @10
    vy
    vz
    wps
    @5
    @8
    @9
    wps
    @5
    @8
    w3a
    #
    wch
    @9
    bnj1379.5
    wch
    @9
    vf
    wch
    wth
    @9
    vf
    wch
    @23
    @4
    @12
    wcel
    #
    wth
    vf
    wps
    @5
    @8
    @23
    @26
    wa
    vf
    wex
    wch
    bnj1379.5
    @5
    @26
    vf
    cA
    @5
    @26
    vf
    cA
    wrex
    vf
    @4
    cA
    eluni2
    biimpi
    bnj1196
    bnj836
    bnj1379.6
    wch
    vf
    wch
    @25
    vf
    bnj1379.5
    wps
    @5
    @8
    vf
    @22
    @5
    vf
    nfv
    @8
    vf
    nfv
    nf3an
    nfxfr
    nf5ri
    bnj1345
    wth
    @9
    vg
    wth
    wta
    @9
    vg
    wth
    @15
    cA
    wcel
    #
    @7
    @15
    wcel
    #
    wta
    vg
    wth
    @8
    @27
    @28
    wa
    vg
    wex
    wch
    @23
    @26
    @8
    wth
    bnj1379.6
    wch
    wps
    @5
    @8
    bnj1379.5
    simp3bi
    bnj835
    @8
    @28
    vg
    cA
    @8
    @28
    vg
    cA
    wrex
    vg
    @7
    cA
    eluni2
    biimpi
    bnj1196
    syl
    bnj1379.7
    wth
    vg
    wth
    wch
    @23
    @26
    w3a
    vg
    bnj1379.6
    wch
    @23
    @26
    vg
    wch
    @25
    vg
    bnj1379.5
    wps
    @5
    @8
    vg
    wps
    @20
    vg
    bnj1379.3
    wph
    @19
    vg
    wph
    vg
    nfv
    @17
    vf
    vg
    cA
    cA
    nfra2
    nfan
    nfxfr
    @5
    vg
    nfv
    @8
    vg
    nfv
    nf3an
    nfxfr
    @23
    vg
    nfv
    @26
    vg
    nfv
    nf3an
    nfxfr
    nf5ri
    bnj1345
    wta
    @2
    @12
    cfv
    #
    @2
    @15
    cfv
    #
    @3
    @6
    wta
    @2
    @14
    cfv
    #
    @2
    @16
    cfv
    #
    @29
    @30
    wta
    @2
    @14
    @16
    wta
    @17
    vg
    cA
    wta
    @18
    vf
    cA
    wth
    @27
    @28
    @19
    wta
    bnj1379.7
    wch
    @23
    @26
    @19
    wth
    bnj1379.6
    wps
    @5
    @8
    @19
    wch
    bnj1379.5
    wps
    wph
    @19
    bnj1379.3
    simprbi
    bnj835
    bnj835
    bnj835
    wch
    @23
    wth
    wta
    @27
    @28
    @26
    bnj1379.6
    bnj1379.7
    bnj1219
    #
    bnj1294
    wta
    wth
    @27
    @28
    bnj1379.7
    simp2bi
    #
    bnj1294
    fveq1d
    wta
    @2
    cD
    wcel
    #
    @31
    @29
    wceq
    wta
    @2
    @12
    cdm
    #
    @15
    cdm
    #
    cin
    cD
    wta
    @36
    @37
    @2
    wta
    @26
    @2
    @36
    wcel
    wth
    @27
    @28
    @26
    wta
    bnj1379.7
    wth
    wch
    @23
    @26
    bnj1379.6
    simp3bi
    bnj835
    #
    @2
    @3
    @12
    vx
    vex
    #
    vy
    vex
    opeldm
    syl
    wth
    @27
    @28
    @2
    @37
    wcel
    wta
    bnj1379.7
    @2
    @6
    @15
    @39
    vz
    vex
    opeldm
    bnj837
    elind
    bnj1379.2
    syl6eleqr
    #
    @2
    cD
    @12
    fvres
    syl
    wta
    @35
    @32
    @30
    wceq
    @40
    @2
    cD
    @15
    fvres
    syl
    3eqtr3d
    wta
    @21
    @26
    @29
    @3
    wceq
    wta
    @21
    vf
    cA
    wth
    @27
    @28
    @21
    vf
    cA
    wral
    #
    wta
    bnj1379.7
    wch
    @23
    @26
    @41
    wth
    bnj1379.6
    wps
    @5
    @8
    @41
    wch
    bnj1379.5
    wph
    @19
    @41
    wps
    bnj1379.3
    wph
    @41
    bnj1379.1
    biimpi
    bnj832
    bnj835
    bnj835
    bnj835
    #
    @33
    bnj1294
    @38
    @2
    @3
    @12
    funopfv
    sylc
    wta
    @15
    wfun
    #
    @28
    @30
    @6
    wceq
    wta
    @43
    vg
    cA
    wta
    @41
    @43
    vg
    cA
    wral
    @42
    @21
    @43
    vf
    vg
    cA
    @12
    @15
    funeq
    cbvralv
    sylib
    @34
    bnj1294
    wta
    wth
    @27
    @28
    bnj1379.7
    simp3bi
    @2
    @6
    @15
    funopfv
    sylc
    3eqtr3d
    bnj593
    bnj937
    bnj593
    bnj937
    sylbir
    3expib
    alrimivv
    alrimiv
    vx
    vy
    vz
    @0
    dffun4
    sylanbrc
end
