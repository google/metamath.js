include "wf.mm"
include "wf1.mm"
include "frgrncvvdeqlem4.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "simpr.mm"
include "wcel.mm"
include "wn.mm"
include "ffvelrn.mm"
include "ad2ant2lr.mm"
include "adantr.mm"
include "wnel.mm"
include "frgrncvvdeqlem1.mm"
include "cpr.mm"
include "crio.mm"
include "cmpt.mm"
include "preq1.mm"
include "eleq1d.mm"
include "riotabidv.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "frgrncvvdeqlem6.mm"
include "anim12dan.mm"
include "wb.mm"
include "preq2.mm"
include "anbi2d.mm"
include "eqcoms.mm"
include "biimpa.mm"
include "wne.mm"
include "df-ne.mm"
include "cfrgr.mm"
include "frgrnbnb.mm"
include "syl3an1.mm"
include "3expa.mm"
include "df-nel.mm"
include "eleq1.mm"
include "pm2.24d.mm"
include "expcom.mm"
include "com13.mm"
include "sylbi.mm"
include "com12.mm"
include "syl6.mm"
include "com23.mm"
include "sylbir.mm"
include "syl5com.mm"
include "com24.mm"
include "mpcom.mm"
include "ex.mm"
include "com3r.mm"
include "com15.mm"
include "expd.mm"
include "imp42.mm"
include "mpid.mm"
include "pm2.18d.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"
include "mpdan.mm"

theorem frgrncvvdeqlem8
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cE: class E
  let cG: class G
  let cN: class N
  let cV: class V
  let cX: class X
  let cY: class Y
  let vn: setvar n
  let vu: setvar u
  let vw: setvar w
  assume frgrncvvdeq.v1: |- V = ( Vtx ` G )
  assume frgrncvvdeq.e: |- E = ( Edg ` G )
  assume frgrncvvdeq.nx: |- D = ( G NeighbVtx X )
  assume frgrncvvdeq.ny: |- N = ( G NeighbVtx Y )
  assume frgrncvvdeq.x: |- ( ph -> X e. V )
  assume frgrncvvdeq.y: |- ( ph -> Y e. V )
  assume frgrncvvdeq.ne: |- ( ph -> X =/= Y )
  assume frgrncvvdeq.xy: |- ( ph -> Y e/ D )
  assume frgrncvvdeq.f: |- ( ph -> G e. FriendGraph )
  assume frgrncvvdeq.a: |- A = ( x e. D |-> ( iota_ y e. N { x , y } e. E ) )

  disjoint G y
  disjoint V y
  disjoint Y y
  disjoint x y
  disjoint E y
  disjoint N y
  disjoint D x
  disjoint N x
  disjoint ph x
  disjoint D y
  disjoint E x
  disjoint D n
  disjoint E n
  disjoint n y
  disjoint G n
  disjoint N n
  disjoint V n
  disjoint Y n
  disjoint n ph
  disjoint n x
  disjoint A u
  disjoint A w
  disjoint u w
  disjoint D u
  disjoint D w
  disjoint u y
  disjoint w y
  disjoint E u
  disjoint E w
  disjoint u x
  disjoint w x
  disjoint N u
  disjoint N w
  disjoint ph u
  disjoint ph w
  assert |- ( ph -> A : D -1-1-> N )

  proof
    wph
    cD
    cN
    cA
    wf
    #
    cD
    cN
    cA
    wf1
    #
    wph
    vx
    vy
    cA
    cD
    cE
    cG
    cN
    cV
    cX
    cY
    frgrncvvdeq.v1
    frgrncvvdeq.e
    frgrncvvdeq.nx
    frgrncvvdeq.ny
    frgrncvvdeq.x
    frgrncvvdeq.y
    frgrncvvdeq.ne
    frgrncvvdeq.xy
    frgrncvvdeq.f
    frgrncvvdeq.a
    frgrncvvdeqlem4
    wph
    @0
    wa
    #
    @0
    vu
    cv
    #
    cA
    cfv
    #
    vw
    cv
    #
    cA
    cfv
    #
    wceq
    #
    @3
    @5
    wceq
    #
    wi
    #
    vw
    cD
    wral
    vu
    cD
    wral
    @1
    wph
    @0
    simpr
    @2
    @9
    vu
    vw
    cD
    cD
    @2
    @3
    cD
    wcel
    #
    @5
    cD
    wcel
    #
    wa
    #
    wa
    #
    @7
    @8
    @13
    @7
    wa
    #
    @8
    @14
    @8
    wn
    #
    @4
    cN
    wcel
    #
    @8
    @13
    @16
    @7
    @0
    @10
    @16
    wph
    @11
    cD
    cN
    @3
    cA
    ffvelrn
    ad2ant2lr
    adantr
    @2
    @10
    @11
    @7
    @15
    @16
    @8
    wi
    #
    wi
    #
    wph
    @10
    @11
    @7
    @18
    wi
    #
    wi
    wi
    @0
    wph
    @10
    @11
    @19
    cX
    cN
    wnel
    #
    wph
    @12
    @19
    wi
    wph
    vx
    vy
    cA
    cD
    cE
    cG
    cN
    cV
    cX
    cY
    frgrncvvdeq.v1
    frgrncvvdeq.e
    frgrncvvdeq.nx
    frgrncvvdeq.ny
    frgrncvvdeq.x
    frgrncvvdeq.y
    frgrncvvdeq.ne
    frgrncvvdeq.xy
    frgrncvvdeq.f
    frgrncvvdeq.a
    frgrncvvdeqlem1
    @15
    wph
    @12
    @7
    @20
    @17
    wph
    @12
    @15
    @7
    @20
    @17
    wi
    #
    wi
    #
    wph
    @12
    @15
    @22
    wi
    #
    @3
    @4
    cpr
    cE
    wcel
    #
    @5
    @6
    cpr
    #
    cE
    wcel
    #
    wa
    #
    wph
    @12
    wa
    #
    @23
    wph
    @10
    @24
    @11
    @26
    wph
    vu
    vy
    cA
    cD
    cE
    cG
    cN
    cV
    cX
    cY
    frgrncvvdeq.v1
    frgrncvvdeq.e
    frgrncvvdeq.nx
    frgrncvvdeq.ny
    frgrncvvdeq.x
    frgrncvvdeq.y
    frgrncvvdeq.ne
    frgrncvvdeq.xy
    frgrncvvdeq.f
    cA
    vx
    cD
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vy
    cN
    crio
    #
    cmpt
    #
    vu
    cD
    @3
    @30
    cpr
    #
    cE
    wcel
    #
    vy
    cN
    crio
    #
    cmpt
    frgrncvvdeq.a
    vx
    vu
    cD
    @33
    @37
    @29
    @3
    wceq
    #
    @32
    @36
    vy
    cN
    @38
    @31
    @35
    cE
    @29
    @3
    @30
    preq1
    eleq1d
    riotabidv
    cbvmptv
    eqtri
    frgrncvvdeqlem6
    wph
    vw
    vy
    cA
    cD
    cE
    cG
    cN
    cV
    cX
    cY
    frgrncvvdeq.v1
    frgrncvvdeq.e
    frgrncvvdeq.nx
    frgrncvvdeq.ny
    frgrncvvdeq.x
    frgrncvvdeq.y
    frgrncvvdeq.ne
    frgrncvvdeq.xy
    frgrncvvdeq.f
    cA
    @34
    vw
    cD
    @5
    @30
    cpr
    #
    cE
    wcel
    #
    vy
    cN
    crio
    #
    cmpt
    frgrncvvdeq.a
    vx
    vw
    cD
    @33
    @41
    @29
    @5
    wceq
    #
    @32
    @40
    vy
    cN
    @42
    @31
    @39
    cE
    @29
    @5
    @30
    preq1
    eleq1d
    riotabidv
    cbvmptv
    eqtri
    frgrncvvdeqlem6
    anim12dan
    @27
    @7
    @15
    @28
    @21
    @7
    @27
    @15
    @28
    @21
    wi
    #
    wi
    @7
    @27
    wa
    @24
    @5
    @4
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @15
    @43
    @7
    @27
    @46
    @27
    @46
    wb
    @6
    @4
    @6
    @4
    wceq
    #
    @26
    @45
    @24
    @47
    @25
    @44
    cE
    @6
    @4
    @5
    preq2
    eleq1d
    anbi2d
    eqcoms
    biimpa
    @15
    @3
    @5
    wne
    #
    @46
    @43
    wi
    @3
    @5
    df-ne
    @48
    @28
    @46
    @21
    @28
    @48
    @46
    @21
    wi
    @28
    @48
    wa
    @46
    @4
    cX
    wceq
    #
    @21
    wph
    @12
    @48
    @46
    @49
    wi
    #
    wph
    cG
    cfrgr
    wcel
    @12
    @48
    @50
    frgrncvvdeq.f
    @4
    cD
    @3
    cE
    cG
    @5
    cX
    frgrncvvdeq.e
    frgrncvvdeq.nx
    frgrnbnb
    syl3an1
    3expa
    @20
    @49
    @17
    @20
    cX
    cN
    wcel
    #
    wn
    #
    @49
    @17
    wi
    cX
    cN
    df-nel
    @16
    @49
    @52
    @8
    @49
    @16
    @52
    @8
    wi
    @49
    @16
    wa
    @51
    @8
    @49
    @16
    @51
    @4
    cX
    cN
    eleq1
    biimpa
    pm2.24d
    expcom
    com13
    sylbi
    com12
    syl6
    expcom
    com23
    sylbir
    syl5com
    expcom
    com24
    mpcom
    ex
    com3r
    com15
    mpcom
    expd
    adantr
    imp42
    mpid
    pm2.18d
    ex
    ralrimivva
    vu
    vw
    cD
    cN
    cA
    dff13
    sylanbrc
    mpdan
end
