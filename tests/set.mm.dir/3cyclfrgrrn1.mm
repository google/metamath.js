include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cv.mm"
include "cpr.mm"
include "w3a.mm"
include "wrex.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wi.mm"
include "2pthfrgrrn2.mm"
include "necom.mm"
include "eldifsn.mm"
include "simplbi2com.mm"
include "sylbi.mm"
include "com12.mm"
include "adantl.mm"
include "imp.mm"
include "wceq.mm"
include "sneq.mm"
include "difeq2d.mm"
include "preq1.mm"
include "eleq1d.mm"
include "anbi1d.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "raleqbidv.mm"
include "rspcv.mm"
include "ad2antrr.mm"
include "preq2.mm"
include "anbi2d.mm"
include "neeq2.mm"
include "sylsyld.mm"
include "2pthfrgrrn.mm"
include "adantr.mm"
include "prcom.mm"
include "eleq1i.mm"
include "anbi12ci.mm"
include "biidd.mm"
include "3anbi123d.mm"
include "rspc2ev.mm"
include "3expa.mm"
include "expcom.mm"
include "3expib.mm"
include "syl5bi.mm"
include "com13.mm"
include "rexlimdva.mm"
include "syl9.mm"
include "exp31.mm"
include "com24.mm"
include "impcom.mm"
include "com15.mm"
include "pm2.43i.mm"
include "com4t.mm"
include "syl.mm"
include "com14.mm"
include "rexlimiv.mm"
include "syl6.mm"
include "pm2.43a.mm"
include "ex.mm"
include "mpcom.mm"
include "3imp.mm"

theorem 3cyclfrgrrn1
  let cA: class A
  let cC: class C
  let cE: class E
  let cG: class G
  let cV: class V
  let vb: setvar b
  let vc: setvar c
  let va: setvar a
  let vx: setvar x
  let vz: setvar z
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v
  assume 3cyclfrgrrn1.v: |- V = ( Vtx ` G )
  assume 3cyclfrgrrn1.e: |- E = ( Edg ` G )

  disjoint A b
  disjoint A c
  disjoint b c
  disjoint E b
  disjoint E c
  disjoint V b
  disjoint V c
  disjoint A a
  disjoint A x
  disjoint A z
  disjoint a x
  disjoint a z
  disjoint x z
  disjoint A y
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint A u
  disjoint A v
  disjoint u v
  disjoint u y
  disjoint v y
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint E a
  disjoint E x
  disjoint E z
  disjoint E y
  disjoint E u
  disjoint E v
  disjoint G a
  disjoint G x
  disjoint G z
  disjoint G u
  disjoint G v
  disjoint G y
  disjoint V a
  disjoint V x
  disjoint V z
  disjoint V y
  disjoint V u
  disjoint V v
  disjoint v x
  assert |- ( ( G e. FriendGraph /\ ( A e. V /\ C e. V ) /\ A =/= C ) -> E. b e. V E. c e. V ( { A , b } e. E /\ { b , c } e. E /\ { c , A } e. E ) )

  proof
    cG
    cfrgr
    wcel
    #
    cA
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    wa
    #
    cA
    cC
    wne
    #
    cA
    vb
    cv
    #
    cpr
    #
    cE
    wcel
    #
    @5
    vc
    cv
    #
    cpr
    #
    cE
    wcel
    #
    @8
    cA
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    vc
    cV
    wrex
    vb
    cV
    wrex
    #
    va
    cv
    #
    vx
    cv
    #
    cpr
    #
    cE
    wcel
    #
    @16
    vz
    cv
    #
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @15
    @16
    wne
    #
    @16
    @19
    wne
    #
    wa
    #
    wa
    #
    vx
    cV
    wrex
    #
    vz
    cV
    @15
    csn
    #
    cdif
    #
    wral
    #
    va
    cV
    wral
    #
    @0
    @3
    @4
    @14
    wi
    wi
    cE
    cG
    cV
    va
    vx
    vz
    3cyclfrgrrn1.v
    3cyclfrgrrn1.e
    2pthfrgrrn2
    @3
    @4
    @31
    @0
    @14
    @3
    @4
    @31
    @0
    @14
    wi
    #
    wi
    @31
    @3
    @4
    wa
    #
    @32
    @33
    @31
    cA
    @16
    cpr
    #
    cE
    wcel
    #
    @16
    cC
    cpr
    #
    cE
    wcel
    #
    wa
    #
    cA
    @16
    wne
    #
    @16
    cC
    wne
    #
    wa
    #
    wa
    #
    vx
    cV
    wrex
    #
    @33
    @32
    wi
    #
    @33
    cC
    cV
    cA
    csn
    #
    cdif
    #
    wcel
    #
    @31
    @35
    @21
    wa
    #
    @39
    @24
    wa
    #
    wa
    #
    vx
    cV
    wrex
    #
    vz
    @46
    wral
    #
    @43
    @3
    @4
    @47
    @2
    @4
    @47
    wi
    @1
    @4
    @2
    @47
    @4
    cC
    cA
    wne
    #
    @2
    @47
    wi
    cA
    cC
    necom
    @47
    @2
    @53
    cC
    cV
    cA
    eldifsn
    simplbi2com
    sylbi
    com12
    adantl
    imp
    @1
    @31
    @52
    wi
    @2
    @4
    @30
    @52
    va
    cA
    cV
    @15
    cA
    wceq
    #
    @27
    @51
    vz
    @29
    @46
    @54
    @28
    @45
    cV
    @15
    cA
    sneq
    difeq2d
    @54
    @26
    @50
    vx
    cV
    @54
    @22
    @48
    @25
    @49
    @54
    @18
    @35
    @21
    @54
    @17
    @34
    cE
    @15
    cA
    @16
    preq1
    eleq1d
    anbi1d
    @54
    @23
    @39
    @24
    @15
    cA
    @16
    neeq1
    anbi1d
    anbi12d
    rexbidv
    raleqbidv
    rspcv
    ad2antrr
    @51
    @43
    vz
    cC
    @46
    @19
    cC
    wceq
    #
    @50
    @42
    vx
    cV
    @55
    @48
    @38
    @49
    @41
    @55
    @21
    @37
    @35
    @55
    @20
    @36
    cE
    @19
    cC
    @16
    preq2
    eleq1d
    anbi2d
    @55
    @24
    @40
    @39
    @19
    cC
    @16
    neeq2
    anbi2d
    anbi12d
    rexbidv
    rspcv
    sylsyld
    @42
    @44
    vx
    cV
    @0
    @42
    @33
    @16
    cV
    wcel
    #
    @14
    @0
    vu
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
    @58
    vv
    cv
    #
    cpr
    #
    cE
    wcel
    #
    wa
    #
    vy
    cV
    wrex
    #
    vv
    cV
    @57
    csn
    #
    cdif
    #
    wral
    #
    vu
    cV
    wral
    #
    @42
    @33
    @56
    @14
    wi
    #
    wi
    wi
    cE
    cG
    cV
    vu
    vy
    vv
    3cyclfrgrrn1.v
    3cyclfrgrrn1.e
    2pthfrgrrn
    @33
    @56
    @69
    @42
    @14
    @1
    @56
    @69
    @42
    @14
    wi
    wi
    #
    wi
    @2
    @4
    @56
    @1
    @71
    @56
    @1
    @71
    wi
    @42
    @56
    @1
    @69
    @56
    @14
    @41
    @38
    @56
    @1
    @69
    @70
    wi
    #
    wi
    wi
    #
    @39
    @38
    @73
    wi
    @40
    @39
    @1
    @56
    @38
    @72
    @39
    @1
    @56
    @38
    @72
    wi
    @39
    @1
    wa
    #
    @56
    wa
    #
    @69
    cA
    @58
    cpr
    #
    cE
    wcel
    #
    @58
    @16
    cpr
    #
    cE
    wcel
    #
    wa
    #
    vy
    cV
    wrex
    #
    @38
    @70
    @75
    @16
    @46
    wcel
    #
    @69
    @77
    @63
    wa
    #
    vy
    cV
    wrex
    #
    vv
    @46
    wral
    #
    @81
    @74
    @56
    @82
    @39
    @56
    @82
    wi
    #
    @1
    @39
    @16
    cA
    wne
    #
    @86
    cA
    @16
    necom
    @82
    @56
    @87
    @16
    cV
    cA
    eldifsn
    simplbi2com
    sylbi
    adantr
    imp
    @74
    @69
    @85
    wi
    #
    @56
    @1
    @88
    @39
    @68
    @85
    vu
    cA
    cV
    @57
    cA
    wceq
    #
    @65
    @84
    vv
    @67
    @46
    @89
    @66
    @45
    cV
    @57
    cA
    sneq
    difeq2d
    @89
    @64
    @83
    vy
    cV
    @89
    @60
    @77
    @63
    @89
    @59
    @76
    cE
    @57
    cA
    @58
    preq1
    eleq1d
    anbi1d
    rexbidv
    raleqbidv
    rspcv
    adantl
    adantr
    @84
    @81
    vv
    @16
    @46
    @61
    @16
    wceq
    #
    @83
    @80
    vy
    cV
    @90
    @63
    @79
    @77
    @90
    @62
    @78
    cE
    @61
    @16
    @58
    preq2
    eleq1d
    anbi2d
    rexbidv
    rspcv
    sylsyld
    @56
    @81
    @38
    @14
    @56
    @80
    @38
    @14
    wi
    vy
    cV
    @38
    @80
    @56
    @58
    cV
    wcel
    #
    wa
    #
    @14
    @35
    @80
    @92
    @14
    wi
    #
    wi
    @37
    @80
    @16
    @58
    cpr
    #
    cE
    wcel
    #
    @58
    cA
    cpr
    #
    cE
    wcel
    #
    wa
    @35
    @93
    @77
    @97
    @79
    @95
    @76
    @96
    cE
    cA
    @58
    prcom
    eleq1i
    @78
    @94
    cE
    @58
    @16
    prcom
    eleq1i
    anbi12ci
    @35
    @95
    @97
    @93
    @92
    @35
    @95
    @97
    w3a
    #
    @14
    @56
    @91
    @98
    @14
    @13
    @98
    @35
    @16
    @8
    cpr
    #
    cE
    wcel
    #
    @12
    w3a
    vb
    vc
    @16
    @58
    cV
    cV
    @5
    @16
    wceq
    #
    @7
    @35
    @10
    @100
    @12
    @12
    @101
    @6
    @34
    cE
    @5
    @16
    cA
    preq2
    eleq1d
    @101
    @9
    @99
    cE
    @5
    @16
    @8
    preq1
    eleq1d
    @101
    @12
    biidd
    3anbi123d
    @8
    @58
    wceq
    #
    @35
    @35
    @100
    @95
    @12
    @97
    @102
    @35
    biidd
    @102
    @99
    @94
    cE
    @8
    @58
    @16
    preq2
    eleq1d
    @102
    @11
    @96
    cE
    @8
    @58
    cA
    preq1
    eleq1d
    3anbi123d
    rspc2ev
    3expa
    expcom
    3expib
    syl5bi
    adantr
    com13
    rexlimdva
    com13
    syl9
    exp31
    com24
    adantr
    impcom
    com15
    pm2.43i
    com12
    ad2antrr
    com4t
    syl
    com14
    rexlimiv
    syl6
    pm2.43a
    ex
    com4t
    mpcom
    3imp
end
