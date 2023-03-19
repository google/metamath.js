include "wpo.mm"
include "cv.mm"
include "wwe.mm"
include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "cima.mm"
include "wbr.mm"
include "wceq.mm"
include "w3o.mm"
include "wor.mm"
include "wss.mm"
include "poss.mm"
include "zorn2lem5.mm"
include "syl11.mm"
include "wi.mm"
include "cfv.mm"
include "wex.mm"
include "wfn.mm"
include "wfun.mm"
include "cvv.mm"
include "wn.mm"
include "crio.mm"
include "cmpt.mm"
include "tfr1.mm"
include "fnfun.mm"
include "wrex.mm"
include "fvelima.mm"
include "df-rex.mm"
include "sylib.mm"
include "ex.mm"
include "anim12d.mm"
include "mp2b.mm"
include "an4.mm"
include "2exbii.mm"
include "eeanv.mm"
include "bitri.mm"
include "sylibr.mm"
include "crab.mm"
include "neeq1i.mm"
include "ralbii.mm"
include "imaeq2.mm"
include "raleqdv.mm"
include "rabbidv.mm"
include "neeq1d.mm"
include "rspccv.mm"
include "sylbi.mm"
include "onelon.mm"
include "anim12dan.mm"
include "word.mm"
include "eloni.mm"
include "ordtri3or.mm"
include "syl2an.mm"
include "eqid.mm"
include "zorn2lem2.mm"
include "adantll.mm"
include "breq12.mm"
include "biimpcd.mm"
include "syl6.mm"
include "com23.mm"
include "adantrrl.mm"
include "imp.mm"
include "fveq2.mm"
include "eqeq12.mm"
include "syl5ib.mm"
include "adantl.mm"
include "adantlr.mm"
include "wb.mm"
include "ancoms.mm"
include "adantrrr.mm"
include "3orim123d.mm"
include "syl5.mm"
include "exp31.mm"
include "com4r.mm"
include "syl6c.mm"
include "exp4a.mm"
include "com3r.mm"
include "a2d.mm"
include "imp4b.mm"
include "exlimdvv.mm"
include "ralrimivv.mm"
include "a1i.mm"
include "jcad.mm"
include "df-so.mm"
include "syl6ibr.mm"

theorem zorn2lem6
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
  disjoint H x
  disjoint u v
  disjoint f u
  disjoint H u
  disjoint f v
  disjoint H v
  disjoint H f
  disjoint f g
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
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
  disjoint D f
  disjoint D u
  disjoint D v
  disjoint D y
  disjoint F f
  disjoint F g
  disjoint F u
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint R f
  disjoint R g
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint C v
  disjoint s x
  disjoint r x
  disjoint a x
  disjoint b x
  disjoint s u
  disjoint r u
  disjoint a u
  disjoint b u
  disjoint s v
  disjoint r v
  disjoint a v
  disjoint b v
  disjoint f s
  disjoint f r
  disjoint a f
  disjoint b f
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
  disjoint f r
  disjoint f s
  disjoint g r
  disjoint g s
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
  disjoint D a
  disjoint D b
  disjoint F a
  disjoint F b
  disjoint F r
  disjoint F s
  disjoint R a
  disjoint R b
  disjoint R r
  disjoint R s
  assert |- ( R Po A -> ( ( ( w We A /\ x e. On ) /\ A. y e. x H =/= (/) ) -> R Or ( F " x ) ) )

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
    vx
    cv
    #
    con0
    wcel
    #
    wa
    #
    cH
    c0
    wne
    #
    vy
    @3
    wral
    #
    wa
    #
    cF
    @3
    cima
    #
    cR
    wpo
    #
    vs
    cv
    #
    vr
    cv
    #
    cR
    wbr
    #
    @11
    @12
    wceq
    #
    @12
    @11
    cR
    wbr
    #
    w3o
    #
    vr
    @9
    wral
    vs
    @9
    wral
    #
    wa
    @9
    cR
    wor
    @0
    @8
    @10
    @17
    @9
    cA
    wss
    @0
    @10
    @8
    @9
    cA
    cR
    poss
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
    syl11
    @8
    @17
    wi
    @0
    @8
    @16
    vs
    vr
    @9
    @9
    @11
    @9
    wcel
    #
    @12
    @9
    wcel
    #
    wa
    #
    vb
    cv
    #
    @3
    wcel
    #
    va
    cv
    #
    @3
    wcel
    #
    wa
    #
    @21
    cF
    cfv
    #
    @11
    wceq
    #
    @23
    cF
    cfv
    #
    @12
    wceq
    #
    wa
    #
    wa
    #
    va
    wex
    vb
    wex
    #
    @8
    @16
    @20
    @22
    @27
    wa
    #
    vb
    wex
    #
    @24
    @29
    wa
    #
    va
    wex
    #
    wa
    #
    @32
    cF
    con0
    wfn
    cF
    wfun
    #
    @20
    @37
    wi
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
    con0
    cF
    fnfun
    @38
    @18
    @34
    @19
    @36
    @38
    @18
    @34
    @38
    @18
    wa
    @27
    vb
    @3
    wrex
    @34
    vb
    @11
    @3
    cF
    fvelima
    @27
    vb
    @3
    df-rex
    sylib
    ex
    @38
    @19
    @36
    @38
    @19
    wa
    @29
    va
    @3
    wrex
    @36
    va
    @12
    @3
    cF
    fvelima
    @29
    va
    @3
    df-rex
    sylib
    ex
    anim12d
    mp2b
    @32
    @33
    @35
    wa
    #
    va
    wex
    vb
    wex
    @37
    @31
    @39
    vb
    va
    @22
    @24
    @27
    @29
    an4
    2exbii
    @33
    @35
    vb
    va
    eeanv
    bitri
    sylibr
    @8
    @31
    @16
    vb
    va
    @5
    @7
    @25
    @30
    @16
    @7
    @25
    vg
    cv
    vz
    cv
    cR
    wbr
    #
    vg
    cF
    @21
    cima
    #
    wral
    #
    vz
    cA
    crab
    #
    c0
    wne
    #
    @40
    vg
    cF
    @23
    cima
    #
    wral
    #
    vz
    cA
    crab
    #
    c0
    wne
    #
    wa
    #
    wi
    #
    @5
    @25
    @30
    @16
    wi
    #
    wi
    @7
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
    #
    c0
    wne
    #
    vy
    @3
    wral
    #
    @50
    @6
    @56
    vy
    @3
    cH
    @55
    c0
    zorn2lem.7
    neeq1i
    ralbii
    @57
    @22
    @44
    @24
    @48
    @56
    @44
    vy
    @21
    @3
    @52
    @21
    wceq
    #
    @55
    @43
    c0
    @58
    @54
    @42
    vz
    cA
    @58
    @40
    vg
    @53
    @41
    @52
    @21
    cF
    imaeq2
    raleqdv
    rabbidv
    neeq1d
    rspccv
    @56
    @48
    vy
    @23
    @3
    @52
    @23
    wceq
    #
    @55
    @47
    c0
    @59
    @54
    @46
    vz
    cA
    @59
    @40
    vg
    @53
    @45
    @52
    @23
    cF
    imaeq2
    raleqdv
    rabbidv
    neeq1d
    rspccv
    anim12d
    sylbi
    @5
    @25
    @49
    @51
    @2
    @4
    @25
    @49
    @51
    wi
    #
    wi
    @4
    @25
    @2
    @60
    @4
    @25
    @2
    @49
    @51
    @4
    @25
    @21
    con0
    wcel
    #
    @23
    con0
    wcel
    #
    wa
    #
    @63
    @2
    @49
    wa
    #
    @51
    wi
    @4
    @25
    @63
    @4
    @22
    @61
    @24
    @62
    @3
    @21
    onelon
    @3
    @23
    onelon
    anim12dan
    ex
    #
    @65
    @63
    @64
    @30
    @63
    @16
    @63
    @64
    @30
    @63
    @16
    wi
    @63
    @21
    @23
    wcel
    #
    @21
    @23
    wceq
    #
    @23
    @21
    wcel
    #
    w3o
    #
    @63
    @64
    wa
    #
    @30
    wa
    #
    @16
    @61
    @21
    word
    @23
    word
    @69
    @62
    @21
    eloni
    @23
    eloni
    @21
    @23
    ordtri3or
    syl2an
    @71
    @66
    @13
    @67
    @14
    @68
    @15
    @70
    @30
    @66
    @13
    wi
    #
    @63
    @2
    @48
    @30
    @72
    wi
    @44
    @63
    @2
    @48
    wa
    #
    wa
    #
    @66
    @30
    @13
    @74
    @66
    @26
    @28
    cR
    wbr
    #
    @30
    @13
    wi
    @62
    @73
    @66
    @75
    wi
    @61
    va
    vb
    vz
    vw
    vv
    vu
    cA
    cC
    @47
    cR
    vf
    vg
    cF
    zorn2lem.3
    zorn2lem.4
    @47
    eqid
    zorn2lem2
    adantll
    @30
    @75
    @13
    @26
    @11
    @28
    @12
    cR
    breq12
    biimpcd
    syl6
    com23
    adantrrl
    imp
    @30
    @67
    @14
    wi
    @70
    @67
    @26
    @28
    wceq
    @30
    @14
    @21
    @23
    cF
    fveq2
    @26
    @11
    @28
    @12
    eqeq12
    syl5ib
    adantl
    @70
    @30
    @68
    @15
    wi
    #
    @63
    @2
    @44
    @30
    @76
    wi
    @48
    @63
    @2
    @44
    wa
    #
    wa
    #
    @68
    @30
    @15
    @78
    @68
    @28
    @26
    cR
    wbr
    #
    @30
    @15
    wi
    @61
    @77
    @68
    @79
    wi
    @62
    vb
    va
    vz
    vw
    vv
    vu
    cA
    cC
    @43
    cR
    vf
    vg
    cF
    zorn2lem.3
    zorn2lem.4
    @43
    eqid
    zorn2lem2
    adantlr
    @30
    @79
    @15
    @29
    @27
    @79
    @15
    wb
    @28
    @12
    @26
    @11
    cR
    breq12
    ancoms
    biimpcd
    syl6
    com23
    adantrrr
    imp
    3orim123d
    syl5
    exp31
    com4r
    syl6c
    exp4a
    com3r
    imp
    a2d
    syl5
    imp4b
    exlimdvv
    syl5
    ralrimivv
    a1i
    jcad
    vs
    vr
    @9
    cR
    df-so
    syl6ibr
end
