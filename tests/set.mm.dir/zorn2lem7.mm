include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wpo.mm"
include "cv.mm"
include "wss.mm"
include "wor.mm"
include "wa.mm"
include "wbr.mm"
include "weq.mm"
include "wo.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wal.mm"
include "wn.mm"
include "wwe.mm"
include "wex.mm"
include "ween.mm"
include "c0.mm"
include "wceq.mm"
include "con0.mm"
include "wne.mm"
include "zorn2lem4.mm"
include "cima.mm"
include "crab.mm"
include "imaeq2.mm"
include "raleqdv.mm"
include "rabbidv.mm"
include "3eqtr4g.mm"
include "eqeq1d.mm"
include "onminex.mm"
include "df-ne.mm"
include "ralbii.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "sylibr.mm"
include "zorn2lem5.mm"
include "a1i.mm"
include "zorn2lem6.mm"
include "jcad.mm"
include "wfn.mm"
include "wfun.mm"
include "cvv.mm"
include "crio.mm"
include "cmpt.mm"
include "tfr1.mm"
include "fnfun.mm"
include "vex.mm"
include "funimaex.mm"
include "mp2b.mm"
include "sseq1.mm"
include "soeq2.mm"
include "anbi12d.mm"
include "raleq.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "spcv.mm"
include "sylan9.mm"
include "adantld.mm"
include "imp.mm"
include "noel.mm"
include "sseld.mm"
include "w3a.mm"
include "3anass.mm"
include "potr.mm"
include "sylan2br.mm"
include "expcomd.mm"
include "breq1.mm"
include "biimprcd.mm"
include "adantl.mm"
include "jaod.mm"
include "exp42.mm"
include "sylan9r.mm"
include "com24.mm"
include "com23.mm"
include "imp31.mm"
include "a2d.mm"
include "ralimdv2.mm"
include "cbvralv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "elrab.mm"
include "wb.mm"
include "eqeq1i.mm"
include "eleq2.mm"
include "sylbi.mm"
include "syl5bbr.mm"
include "biimpd.mm"
include "expdimp.mm"
include "syl5bi.mm"
include "exp32.mm"
include "com34.mm"
include "mtoi.mm"
include "exp4a.mm"
include "ex.mm"
include "com4r.mm"
include "pm2.43a.mm"
include "impd.mm"
include "com4l.mm"
include "ralrimdv.mm"
include "expd.mm"
include "reximdvai.mm"
include "com12.mm"
include "adantr.mm"
include "imp32.mm"
include "mpd.mm"
include "exp45.mm"
include "imp4a.mm"
include "com3l.mm"
include "rexlimiv.mm"
include "3syl.mm"
include "adantlr.mm"
include "pm2.43i.mm"
include "expcom.mm"
include "exlimiv.mm"
include "3impib.mm"

theorem zorn2lem7
  let vx: setvar x
  let vy: setvar y
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
  let cH: class H
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  assume zorn2lem.3: |- F = recs ( ( f e. _V |-> ( iota_ v e. C A. u e. C -. u w v ) ) )
  assume zorn2lem.4: |- C = { z e. A | A. g e. ran f g R z }
  assume zorn2lem.5: |- D = { z e. A | A. g e. ( F " x ) g R z }
  assume zorn2lem.7: |- H = { z e. A | A. g e. ( F " y ) g R z }

  disjoint u x
  disjoint v x
  disjoint f x
  disjoint s x
  disjoint r x
  disjoint a x
  disjoint b x
  disjoint H x
  disjoint u v
  disjoint f u
  disjoint s u
  disjoint r u
  disjoint a u
  disjoint b u
  disjoint H u
  disjoint f v
  disjoint s v
  disjoint r v
  disjoint a v
  disjoint b v
  disjoint H v
  disjoint f s
  disjoint f r
  disjoint a f
  disjoint b f
  disjoint H f
  disjoint r s
  disjoint a s
  disjoint b s
  disjoint H s
  disjoint a r
  disjoint b r
  disjoint H r
  disjoint a b
  disjoint H a
  disjoint H b
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
  disjoint f g
  disjoint f r
  disjoint f s
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g r
  disjoint g s
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
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
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint D a
  disjoint D b
  disjoint D f
  disjoint D u
  disjoint D v
  disjoint D y
  disjoint F a
  disjoint F b
  disjoint F f
  disjoint F g
  disjoint F r
  disjoint F s
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R a
  disjoint R b
  disjoint R f
  disjoint R g
  disjoint R r
  disjoint R s
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint C v
  assert |- ( ( A e. dom card /\ R Po A /\ A. s ( ( s C_ A /\ R Or s ) -> E. a e. A A. r e. s ( r R a \/ r = a ) ) ) -> E. a e. A A. b e. A -. a R b )

  proof
    cA
    ccrd
    cdm
    wcel
    #
    cA
    cR
    wpo
    #
    vs
    cv
    #
    cA
    wss
    #
    @2
    cR
    wor
    #
    wa
    #
    vr
    cv
    #
    va
    cv
    #
    cR
    wbr
    #
    vr
    va
    weq
    #
    wo
    #
    vr
    @2
    wral
    #
    va
    cA
    wrex
    #
    wi
    #
    vs
    wal
    #
    @7
    vb
    cv
    #
    cR
    wbr
    #
    wn
    #
    vb
    cA
    wral
    #
    va
    cA
    wrex
    #
    @0
    cA
    vw
    cv
    #
    wwe
    #
    vw
    wex
    @1
    @14
    wa
    #
    @19
    wi
    #
    cA
    vw
    ween
    @21
    @23
    vw
    @22
    @21
    @19
    @22
    @21
    wa
    #
    @19
    @1
    @21
    @24
    @19
    wi
    #
    @14
    @1
    @21
    wa
    cD
    c0
    wceq
    #
    vx
    con0
    wrex
    #
    @26
    cH
    c0
    wne
    #
    vy
    vx
    cv
    #
    wral
    #
    wa
    #
    vx
    con0
    wrex
    #
    @25
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
    zorn2lem4
    @27
    @26
    cH
    c0
    wceq
    #
    wn
    #
    vy
    @29
    wral
    #
    wa
    #
    vx
    con0
    wrex
    @32
    @26
    @33
    vx
    vy
    vx
    vy
    weq
    #
    cD
    cH
    c0
    @37
    vg
    cv
    #
    vz
    cv
    #
    cR
    wbr
    #
    vg
    cF
    @29
    cima
    #
    wral
    #
    vz
    cA
    crab
    #
    @40
    vg
    cF
    vy
    cv
    #
    cima
    #
    wral
    #
    vz
    cA
    crab
    cD
    cH
    @37
    @42
    @46
    vz
    cA
    @37
    @40
    vg
    @41
    @45
    @29
    @44
    cF
    imaeq2
    raleqdv
    rabbidv
    zorn2lem.5
    zorn2lem.7
    3eqtr4g
    eqeq1d
    onminex
    @31
    @36
    vx
    con0
    @30
    @35
    @26
    @28
    @34
    vy
    @29
    cH
    c0
    df-ne
    ralbii
    anbi2i
    rexbii
    sylibr
    @31
    @25
    vx
    con0
    @24
    @29
    con0
    wcel
    #
    @31
    @19
    @24
    @47
    @26
    @30
    @19
    @22
    @21
    @47
    @26
    @30
    @19
    wi
    #
    wi
    @22
    @26
    @21
    @47
    wa
    #
    @48
    @22
    @26
    @49
    @30
    @19
    @22
    @26
    @49
    @30
    wa
    #
    wa
    #
    wa
    @10
    vr
    @41
    wral
    #
    va
    cA
    wrex
    #
    @19
    @22
    @51
    @53
    @22
    @50
    @53
    @26
    @1
    @50
    @41
    cA
    wss
    #
    @41
    cR
    wor
    #
    wa
    #
    @14
    @53
    @1
    @50
    @54
    @55
    @50
    @54
    wi
    @1
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
    cH
    zorn2lem.3
    zorn2lem.4
    zorn2lem.5
    zorn2lem.7
    zorn2lem5
    #
    a1i
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
    cH
    zorn2lem.3
    zorn2lem.4
    zorn2lem.5
    zorn2lem.7
    zorn2lem6
    jcad
    @13
    @56
    @53
    wi
    vs
    @41
    cF
    con0
    wfn
    cF
    wfun
    @41
    cvv
    wcel
    cF
    vf
    cvv
    vu
    cv
    vv
    cv
    @20
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
    con0
    cF
    fnfun
    cF
    @29
    vx
    vex
    funimaex
    mp2b
    @2
    @41
    wceq
    #
    @5
    @56
    @12
    @53
    @58
    @3
    @54
    @4
    @55
    @2
    @41
    cA
    sseq1
    @2
    @41
    cR
    soeq2
    anbi12d
    @58
    @11
    @52
    va
    cA
    @10
    vr
    @2
    @41
    raleq
    rexbidv
    imbi12d
    spcv
    sylan9
    adantld
    imp
    @22
    @26
    @50
    @53
    @19
    wi
    #
    @1
    @26
    @50
    @59
    wi
    #
    wi
    @14
    @26
    @1
    @60
    @26
    @1
    @50
    @59
    @26
    @1
    @50
    wa
    #
    wa
    #
    @52
    @18
    va
    cA
    @62
    @7
    cA
    wcel
    #
    @52
    @18
    @62
    @63
    @52
    wa
    @17
    vb
    cA
    @62
    @63
    @52
    @15
    cA
    wcel
    #
    @17
    wi
    @64
    @62
    @63
    @52
    @17
    @64
    @26
    @61
    @63
    @52
    @17
    wi
    #
    wi
    #
    @26
    @64
    @61
    @66
    wi
    @26
    @64
    @61
    @64
    @66
    @26
    @64
    @61
    @64
    @66
    wi
    wi
    @26
    @64
    wa
    #
    @61
    @63
    @64
    @65
    @67
    @61
    @63
    @64
    @65
    @67
    @61
    @63
    @64
    wa
    #
    @52
    @17
    @67
    @61
    @68
    wa
    #
    wa
    @52
    wa
    @16
    @15
    c0
    wcel
    #
    @15
    noel
    @67
    @69
    @52
    @16
    @70
    wi
    @67
    @69
    @16
    @52
    @70
    @67
    @69
    @16
    @52
    @70
    wi
    @69
    @16
    wa
    #
    @52
    @6
    @15
    cR
    wbr
    #
    vr
    @41
    wral
    #
    @67
    @70
    @71
    @10
    @72
    vr
    @41
    @41
    @71
    @6
    @41
    wcel
    #
    @10
    @72
    @61
    @68
    @16
    @74
    @10
    @72
    wi
    #
    wi
    #
    @61
    @16
    @68
    @76
    @61
    @74
    @68
    @16
    @75
    @50
    @74
    @6
    cA
    wcel
    #
    @1
    @68
    @16
    @75
    wi
    wi
    @50
    @41
    cA
    @6
    @57
    sseld
    @1
    @77
    @68
    @16
    @75
    @1
    @77
    @68
    wa
    #
    wa
    #
    @16
    wa
    @8
    @72
    @9
    @79
    @16
    @8
    @72
    wi
    @79
    @8
    @16
    @72
    @78
    @1
    @77
    @63
    @64
    w3a
    @8
    @16
    wa
    @72
    wi
    @77
    @63
    @64
    3anass
    cA
    @6
    @7
    @15
    cR
    potr
    sylan2br
    expcomd
    imp
    @16
    @9
    @72
    wi
    @79
    @9
    @72
    @16
    @6
    @7
    @15
    cR
    breq1
    biimprcd
    adantl
    jaod
    exp42
    sylan9r
    com24
    com23
    imp31
    a2d
    ralimdv2
    @73
    @38
    @15
    cR
    wbr
    #
    vg
    @41
    wral
    #
    @67
    @70
    @72
    @80
    vr
    vg
    @41
    @6
    @38
    @15
    cR
    breq1
    cbvralv
    @26
    @64
    @81
    @70
    @26
    @64
    @81
    wa
    #
    @70
    @82
    @15
    @43
    wcel
    #
    @26
    @70
    @42
    @81
    vz
    @15
    cA
    vz
    vb
    weq
    @40
    @80
    vg
    @41
    @39
    @15
    @38
    cR
    breq2
    ralbidv
    elrab
    @26
    @43
    c0
    wceq
    @83
    @70
    wb
    cD
    @43
    c0
    zorn2lem.5
    eqeq1i
    @43
    c0
    @15
    eleq2
    sylbi
    syl5bbr
    biimpd
    expdimp
    syl5bi
    sylan9r
    exp32
    com34
    imp31
    mtoi
    exp42
    exp4a
    com34
    ex
    com4r
    pm2.43a
    impd
    com4l
    impd
    ralrimdv
    expd
    reximdvai
    exp32
    com12
    adantr
    imp32
    mpd
    exp45
    com23
    expdimp
    imp4a
    com3l
    rexlimiv
    3syl
    adantlr
    pm2.43i
    expcom
    exlimiv
    sylbi
    3impib
end
