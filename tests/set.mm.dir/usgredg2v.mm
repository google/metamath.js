include "cusgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "crio.mm"
include "wral.mm"
include "weq.mm"
include "wi.mm"
include "wf1.mm"
include "usgredg2vlem1.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "wn.mm"
include "cdm.mm"
include "crn.mm"
include "wb.mm"
include "usgrf1.mm"
include "crab.mm"
include "elrabi.mm"
include "eleq2s.mm"
include "anim12i.mm"
include "f1fveq.mm"
include "syl2an.mm"
include "bicomd.mm"
include "notbid.mm"
include "simpl.mm"
include "preq1.mm"
include "eqeq2d.mm"
include "cbvriotav.mm"
include "usgredg2vlem2.mm"
include "mpisyl.mm"
include "simpr.mm"
include "eqeq12d.mm"
include "wo.mm"
include "cvv.mm"
include "riotaex.mm"
include "a1i.mm"
include "id.mm"
include "preq12bg.mm"
include "syl22anc.mm"
include "adantl.mm"
include "ioran.mm"
include "ianor.mm"
include "eqeq12i.mm"
include "notbii.mm"
include "biimpi.mm"
include "a1d.mm"
include "eqid.mm"
include "pm2.24i.mm"
include "jaoi.mm"
include "sylbi.mm"
include "com12.mm"
include "sylbid.mm"
include "con4d.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "riotabidv.mm"
include "f1mpt.mm"
include "sylanbrc.mm"

theorem usgredg2v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cY: class Y
  let cI: class I
  let vw: setvar w
  let vu: setvar u
  assume usgredg2v.v: |- V = ( Vtx ` G )
  assume usgredg2v.e: |- E = ( iEdg ` G )
  assume usgredg2v.a: |- A = { x e. dom E | N e. ( E ` x ) }
  assume usgredg2v.f: |- F = ( y e. A |-> ( iota_ z e. V ( E ` y ) = { z , N } ) )

  disjoint x z
  disjoint A y
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint x y
  disjoint y z
  disjoint G y
  disjoint N y
  disjoint V y
  disjoint E x
  disjoint E z
  disjoint x z
  disjoint G z
  disjoint N x
  disjoint N z
  disjoint V z
  disjoint Y x
  disjoint Y z
  disjoint I z
  disjoint A w
  disjoint w y
  disjoint E w
  disjoint w x
  disjoint w z
  disjoint F w
  disjoint G w
  disjoint N u
  disjoint N w
  disjoint u w
  disjoint u y
  disjoint V u
  disjoint V w
  disjoint E u
  disjoint u z
  assert |- ( ( G e. USGraph /\ N e. V ) -> F : A -1-1-> V )

  proof
    cG
    cusgr
    wcel
    #
    cN
    cV
    wcel
    #
    wa
    #
    vy
    cv
    #
    cE
    cfv
    #
    vz
    cv
    #
    cN
    cpr
    #
    wceq
    #
    vz
    cV
    crio
    #
    cV
    wcel
    #
    vy
    cA
    wral
    #
    @8
    vw
    cv
    #
    cE
    cfv
    #
    @6
    wceq
    #
    vz
    cV
    crio
    #
    wceq
    #
    vy
    vw
    weq
    #
    wi
    #
    vw
    cA
    wral
    vy
    cA
    wral
    cA
    cV
    cF
    wf1
    @0
    @10
    @1
    @0
    @9
    vy
    cA
    vx
    vz
    cA
    cE
    cG
    cN
    cV
    @3
    usgredg2v.v
    usgredg2v.e
    usgredg2v.a
    usgredg2vlem1
    ralrimiva
    adantr
    @2
    @17
    vy
    vw
    cA
    cA
    @2
    @3
    cA
    wcel
    #
    @11
    cA
    wcel
    #
    wa
    #
    wa
    #
    @16
    @15
    @21
    @16
    wn
    @4
    @12
    wceq
    #
    wn
    #
    @15
    wn
    #
    @21
    @16
    @22
    @21
    @22
    @16
    @2
    cE
    cdm
    #
    cE
    crn
    #
    cE
    wf1
    #
    @3
    @25
    wcel
    #
    @11
    @25
    wcel
    #
    wa
    @22
    @16
    wb
    @20
    @0
    @27
    @1
    cE
    cG
    usgredg2v.e
    usgrf1
    adantr
    @18
    @28
    @19
    @29
    @28
    @3
    cN
    vx
    cv
    cE
    cfv
    wcel
    #
    vx
    @25
    crab
    #
    cA
    @30
    vx
    @3
    @25
    elrabi
    usgredg2v.a
    eleq2s
    @29
    @11
    @31
    cA
    @30
    vx
    @11
    @25
    elrabi
    usgredg2v.a
    eleq2s
    anim12i
    @25
    @26
    @3
    @11
    cE
    f1fveq
    syl2an
    bicomd
    notbid
    @21
    @23
    @4
    vu
    cv
    #
    cN
    cpr
    #
    wceq
    #
    vu
    cV
    crio
    #
    cN
    cpr
    #
    @12
    @33
    wceq
    #
    vu
    cV
    crio
    #
    cN
    cpr
    #
    wceq
    #
    wn
    #
    @24
    @21
    @22
    @40
    @21
    @4
    @36
    @12
    @39
    @21
    @0
    @18
    wa
    @35
    @8
    wceq
    @4
    @36
    wceq
    @2
    @0
    @20
    @18
    @0
    @1
    simpl
    #
    @18
    @19
    simpl
    anim12i
    @34
    @7
    vu
    vz
    cV
    vu
    vz
    weq
    #
    @33
    @6
    @4
    @32
    @5
    cN
    preq1
    #
    eqeq2d
    cbvriotav
    #
    vx
    vz
    cA
    cE
    cG
    @35
    cN
    cV
    @3
    usgredg2v.v
    usgredg2v.e
    usgredg2v.a
    usgredg2vlem2
    mpisyl
    @21
    @0
    @19
    wa
    @38
    @14
    wceq
    @12
    @39
    wceq
    @2
    @0
    @20
    @19
    @42
    @18
    @19
    simpr
    anim12i
    @37
    @13
    vu
    vz
    cV
    @43
    @33
    @6
    @12
    @44
    eqeq2d
    cbvriotav
    #
    vx
    vz
    cA
    cE
    cG
    @38
    cN
    cV
    @11
    usgredg2v.v
    usgredg2v.e
    usgredg2v.a
    usgredg2vlem2
    mpisyl
    eqeq12d
    notbid
    @2
    @41
    @24
    wi
    @20
    @2
    @41
    @35
    @38
    wceq
    #
    cN
    cN
    wceq
    #
    wa
    #
    @35
    cN
    wceq
    cN
    @38
    wceq
    wa
    #
    wo
    #
    wn
    #
    @24
    @1
    @41
    @52
    wb
    @0
    @1
    @40
    @51
    @1
    @35
    cvv
    wcel
    #
    @1
    @38
    cvv
    wcel
    #
    @1
    @40
    @51
    wb
    @53
    @1
    @34
    vu
    cV
    riotaex
    a1i
    @1
    id
    #
    @54
    @1
    @37
    vu
    cV
    riotaex
    a1i
    @55
    @35
    cN
    @38
    cN
    cvv
    cV
    cvv
    cV
    preq12bg
    syl22anc
    notbid
    adantl
    @0
    @52
    @24
    wi
    @1
    @52
    @0
    @24
    @52
    @49
    wn
    #
    @50
    wn
    #
    wa
    @0
    @24
    wi
    #
    @49
    @50
    ioran
    @56
    @58
    @57
    @56
    @47
    wn
    #
    @48
    wn
    #
    wo
    @58
    @47
    @48
    ianor
    @59
    @58
    @60
    @59
    @24
    @0
    @59
    @24
    @47
    @15
    @35
    @8
    @38
    @14
    @45
    @46
    eqeq12i
    notbii
    biimpi
    a1d
    @48
    @58
    cN
    eqid
    pm2.24i
    jaoi
    sylbi
    adantr
    sylbi
    com12
    adantr
    sylbid
    adantr
    sylbid
    sylbid
    con4d
    ralrimivva
    vy
    vw
    cA
    cV
    @8
    @14
    cF
    usgredg2v.f
    @16
    @7
    @13
    vz
    cV
    @16
    @4
    @12
    @6
    @3
    @11
    cE
    fveq2
    eqeq1d
    riotabidv
    f1mpt
    sylanbrc
end
