include "wpo.mm"
include "cv.mm"
include "wwe.mm"
include "wa.mm"
include "c0.mm"
include "wceq.mm"
include "con0.mm"
include "wrex.mm"
include "crn.mm"
include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "pm3.24.mm"
include "wne.mm"
include "wi.mm"
include "wal.mm"
include "wral.mm"
include "df-ne.mm"
include "ralbii.mm"
include "df-ral.mm"
include "ralnex.mm"
include "3bitr3i.mm"
include "wor.mm"
include "weso.mm"
include "adantr.mm"
include "vex.mm"
include "soex.mm"
include "sylancl.mm"
include "cfv.mm"
include "wfn.mm"
include "wb.mm"
include "wbr.mm"
include "crio.mm"
include "cmpt.mm"
include "tfr1.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "nfv.mm"
include "nfa1.mm"
include "nfan.mm"
include "cima.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "zorn2lem1.mm"
include "sseldi.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "exp32.mm"
include "com12.mm"
include "a2d.mm"
include "spsd.mm"
include "imp.mm"
include "rexlimd.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "ssexd.mm"
include "ex.mm"
include "adantl.mm"
include "ccnv.mm"
include "wfun.mm"
include "zorn2lem3.mm"
include "exp45.mm"
include "com23.mm"
include "imp4a.mm"
include "alrimdv.mm"
include "alimdv.mm"
include "r2al.mm"
include "syl6ibr.mm"
include "cres.mm"
include "wss.mm"
include "ssid.mm"
include "tz7.48lem.mm"
include "mpan.mm"
include "wrel.mm"
include "cdm.mm"
include "fnrel.mm"
include "fndm.mm"
include "eqimssi.mm"
include "relssres.mm"
include "mp2an.mm"
include "cnveqi.mm"
include "funeqi.mm"
include "sylib.mm"
include "syl6.mm"
include "onprc.mm"
include "funrnex.mm"
include "df-rn.mm"
include "eleq1i.mm"
include "dfdm4.mm"
include "eqtr3i.mm"
include "3imtr4g.mm"
include "mtoi.mm"
include "jcad.mm"
include "syl5bir.mm"
include "mt3i.mm"

theorem zorn2lem4
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vr: setvar r
  let vs: setvar s
  let vy: setvar y
  assume zorn2lem.3: |- F = recs ( ( f e. _V |-> ( iota_ v e. C A. u e. C -. u w v ) ) )
  assume zorn2lem.4: |- C = { z e. A | A. g e. ran f g R z }
  assume zorn2lem.5: |- D = { z e. A | A. g e. ( F " x ) g R z }

  disjoint f g
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f z
  disjoint A f
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g z
  disjoint A g
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint D f
  disjoint D u
  disjoint D v
  disjoint F f
  disjoint F g
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F z
  disjoint R f
  disjoint R g
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R z
  disjoint C v
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a r
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b f
  disjoint b g
  disjoint b r
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint f r
  disjoint f s
  disjoint f y
  disjoint g r
  disjoint g s
  disjoint g y
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint A s
  disjoint u y
  disjoint v y
  disjoint w y
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint D a
  disjoint D b
  disjoint D y
  disjoint F a
  disjoint F b
  disjoint F r
  disjoint F s
  disjoint F y
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  disjoint R y
  assert |- ( ( R Po A /\ w We A ) -> E. x e. On D = (/) )

  proof
    cA
    cR
    wpo
    #
    cA
    vw
    cv
    #
    wwe
    #
    wa
    #
    cD
    c0
    wceq
    #
    vx
    con0
    wrex
    #
    cF
    crn
    #
    cvv
    wcel
    #
    @7
    wn
    #
    wa
    #
    @7
    pm3.24
    @5
    wn
    #
    vx
    cv
    #
    con0
    wcel
    #
    cD
    c0
    wne
    #
    wi
    #
    vx
    wal
    #
    @3
    @9
    @13
    vx
    con0
    wral
    @4
    wn
    #
    vx
    con0
    wral
    @15
    @10
    @13
    @16
    vx
    con0
    cD
    c0
    df-ne
    ralbii
    @13
    vx
    con0
    df-ral
    @4
    vx
    con0
    ralnex
    3bitr3i
    @3
    @15
    @7
    @8
    @2
    @15
    @7
    wi
    @0
    @2
    @15
    @7
    @2
    @15
    wa
    #
    @6
    cA
    cvv
    @17
    cA
    @1
    wor
    #
    @1
    cvv
    wcel
    cA
    cvv
    wcel
    @2
    @18
    @15
    cA
    @1
    weso
    adantr
    vw
    vex
    cA
    @1
    cvv
    soex
    sylancl
    @17
    vy
    @6
    cA
    vy
    cv
    #
    @6
    wcel
    #
    @11
    cF
    cfv
    #
    @19
    wceq
    #
    vx
    con0
    wrex
    #
    @17
    @19
    cA
    wcel
    #
    cF
    con0
    wfn
    #
    @20
    @23
    wb
    cF
    vf
    cvv
    vu
    cv
    vv
    cv
    @1
    wbr
    wn
    vu
    cC
    wral
    vv
    cC
    crio
    cmpt
    zorn2lem.3
    tfr1
    #
    vx
    con0
    @19
    cF
    fvelrnb
    ax-mp
    @17
    @22
    @24
    vx
    con0
    @2
    @15
    vx
    @2
    vx
    nfv
    @14
    vx
    nfa1
    nfan
    @24
    vx
    nfv
    @2
    @15
    @12
    @22
    @24
    wi
    #
    wi
    #
    @2
    @14
    @28
    vx
    @2
    @12
    @13
    @27
    @12
    @2
    @13
    @27
    wi
    @12
    @2
    @13
    @27
    @12
    @2
    @13
    wa
    wa
    #
    @21
    cA
    wcel
    @22
    @24
    @29
    cD
    cA
    @21
    cD
    vg
    cv
    vz
    cv
    cR
    wbr
    vg
    cF
    @11
    cima
    wral
    #
    vz
    cA
    crab
    cA
    zorn2lem.5
    @30
    vz
    cA
    ssrab2
    eqsstri
    vx
    vz
    vw
    vv
    vu
    cA
    cC
    cD
    cR
    vf
    vg
    cF
    zorn2lem.3
    zorn2lem.4
    zorn2lem.5
    zorn2lem1
    sseldi
    @21
    @19
    cA
    eleq1
    syl5ibcom
    exp32
    com12
    a2d
    spsd
    imp
    rexlimd
    syl5bi
    ssrdv
    ssexd
    ex
    adantl
    @3
    @15
    cF
    ccnv
    #
    wfun
    #
    @8
    @3
    @15
    @21
    @19
    cF
    cfv
    wceq
    wn
    #
    vy
    @11
    wral
    vx
    con0
    wral
    #
    @32
    @3
    @15
    @12
    @19
    @11
    wcel
    #
    wa
    @33
    wi
    #
    vy
    wal
    #
    vx
    wal
    @34
    @3
    @14
    @37
    vx
    @3
    @14
    @36
    vy
    @3
    @14
    @12
    @35
    @33
    @3
    @12
    @13
    @35
    @33
    wi
    #
    @0
    @2
    @12
    @13
    @38
    wi
    #
    wi
    @0
    @12
    @2
    @39
    @0
    @12
    @2
    @13
    @38
    vx
    vy
    vz
    vw
    vv
    vu
    cA
    cC
    cD
    cR
    vf
    vg
    cF
    zorn2lem.3
    zorn2lem.4
    zorn2lem.5
    zorn2lem3
    exp45
    com23
    imp
    a2d
    imp4a
    alrimdv
    alimdv
    @33
    vx
    vy
    con0
    @11
    r2al
    syl6ibr
    @34
    cF
    con0
    cres
    #
    ccnv
    #
    wfun
    #
    @32
    con0
    con0
    wss
    @34
    @42
    con0
    ssid
    vx
    vy
    con0
    cF
    @26
    tz7.48lem
    mpan
    @41
    @31
    @40
    cF
    cF
    wrel
    #
    cF
    cdm
    #
    con0
    wss
    @40
    cF
    wceq
    @25
    @43
    @26
    con0
    cF
    fnrel
    ax-mp
    @44
    con0
    @25
    @44
    con0
    wceq
    @26
    con0
    cF
    fndm
    ax-mp
    #
    eqimssi
    cF
    con0
    relssres
    mp2an
    cnveqi
    funeqi
    sylib
    syl6
    @32
    @7
    con0
    cvv
    wcel
    #
    onprc
    @32
    @31
    cdm
    #
    cvv
    wcel
    #
    @31
    crn
    #
    cvv
    wcel
    #
    @7
    @46
    @48
    @32
    @50
    cvv
    @31
    funrnex
    com12
    @6
    @47
    cvv
    cF
    df-rn
    eleq1i
    con0
    @49
    cvv
    @44
    con0
    @49
    @45
    cF
    dfdm4
    eqtr3i
    eleq1i
    3imtr4g
    mtoi
    syl6
    jcad
    syl5bir
    mt3i
end
