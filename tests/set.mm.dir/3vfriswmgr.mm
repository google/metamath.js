include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "ctp.mm"
include "wceq.mm"
include "cfrgr.mm"
include "cv.mm"
include "cpr.mm"
include "csn.mm"
include "cdif.mm"
include "wreu.mm"
include "wa.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "wb.mm"
include "frgr3v.mm"
include "exp4b.mm"
include "3imp1.mm"
include "w3o.mm"
include "prcom.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "simpl11.mm"
include "simpl12.mm"
include "simp1.mm"
include "3ad2ant2.mm"
include "adantr.mm"
include "3jca.mm"
include "simp3.mm"
include "anim1i.mm"
include "jca.mm"
include "3vfriswmgrlem.mm"
include "imp.mm"
include "syl2an.mm"
include "simpr2.mm"
include "necom.mm"
include "3ad2ant1.mm"
include "tpcoma.mm"
include "syl6eq.mm"
include "reueq1.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "preq1.mm"
include "eleq1d.mm"
include "reubidv.mm"
include "anbi12d.mm"
include "ralprg.mm"
include "3adant3.mm"
include "mpbird.mm"
include "diftpsn3.mm"
include "3adant1.mm"
include "syl.mm"
include "anbi2d.mm"
include "raleqbidv.mm"
include "3mix3d.mm"
include "sneq.mm"
include "difeq2d.mm"
include "preq2.mm"
include "rextpg.mm"
include "ex.mm"
include "sylbid.mm"
include "expcom.mm"
include "com23.mm"
include "mpcom.mm"
include "com12.mm"
include "difeq1.mm"
include "rexeqbi1dv.mm"
include "imbi2d.mm"

theorem 3vfriswmgr
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let vh: setvar h
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vy: setvar y
  assume 3vfriswmgr.v: |- V = ( Vtx ` G )
  assume 3vfriswmgr.e: |- E = ( Edg ` G )

  disjoint A w
  disjoint B w
  disjoint C w
  disjoint E w
  disjoint G w
  disjoint V w
  disjoint X w
  disjoint Y w
  disjoint A h
  disjoint A v
  disjoint h v
  disjoint h w
  disjoint v w
  disjoint B h
  disjoint B v
  disjoint C h
  disjoint C v
  disjoint E h
  disjoint E v
  disjoint V h
  disjoint V v
  disjoint A y
  disjoint w y
  disjoint B y
  disjoint C y
  disjoint E y
  disjoint G y
  disjoint V y
  disjoint X y
  disjoint Y y
  assert |- ( ( ( A e. X /\ B e. Y /\ C e. Z ) /\ ( A =/= B /\ A =/= C /\ B =/= C ) /\ V = { A , B , C } ) -> ( G e. FriendGraph -> E. h e. V A. v e. ( V \ { h } ) ( { v , h } e. E /\ E! w e. ( V \ { h } ) { v , w } e. E ) ) )

  proof
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cC
    cZ
    wcel
    #
    w3a
    #
    cA
    cB
    wne
    #
    cA
    cC
    wne
    #
    cB
    cC
    wne
    #
    w3a
    #
    cV
    cA
    cB
    cC
    ctp
    #
    wceq
    #
    w3a
    #
    cG
    cfrgr
    wcel
    #
    vv
    cv
    #
    vh
    cv
    #
    cpr
    #
    cE
    wcel
    #
    @12
    vw
    cv
    #
    cpr
    #
    cE
    wcel
    #
    vw
    cV
    @13
    csn
    #
    cdif
    #
    wreu
    #
    wa
    #
    vv
    @20
    wral
    #
    vh
    cV
    wrex
    #
    wi
    #
    @11
    @15
    @18
    vw
    @8
    @19
    cdif
    #
    wreu
    #
    wa
    #
    vv
    @26
    wral
    #
    vh
    @8
    wrex
    #
    wi
    #
    @11
    @10
    @30
    cG
    cusgr
    wcel
    #
    @11
    @10
    @30
    wi
    cG
    frgrusgr
    @32
    @10
    @11
    @30
    @10
    @32
    @31
    @10
    @32
    wa
    #
    @11
    cA
    cB
    cpr
    #
    cE
    wcel
    #
    cB
    cC
    cpr
    #
    cE
    wcel
    #
    cC
    cA
    cpr
    #
    cE
    wcel
    #
    w3a
    #
    @30
    @3
    @7
    @9
    @32
    @11
    @40
    wb
    #
    @3
    @7
    @9
    @32
    @41
    cA
    cB
    cC
    cE
    cG
    cV
    cX
    cY
    cZ
    3vfriswmgr.v
    3vfriswmgr.e
    frgr3v
    exp4b
    3imp1
    @33
    @40
    @30
    @33
    @40
    wa
    #
    @30
    @12
    cA
    cpr
    #
    cE
    wcel
    #
    @18
    vw
    @8
    cA
    csn
    #
    cdif
    #
    wreu
    #
    wa
    #
    vv
    @46
    wral
    #
    @12
    cB
    cpr
    #
    cE
    wcel
    #
    @18
    vw
    @8
    cB
    csn
    #
    cdif
    #
    wreu
    #
    wa
    #
    vv
    @53
    wral
    #
    @12
    cC
    cpr
    #
    cE
    wcel
    #
    @18
    vw
    @8
    cC
    csn
    #
    cdif
    #
    wreu
    #
    wa
    #
    vv
    @60
    wral
    #
    w3o
    #
    @42
    @63
    @49
    @56
    @42
    @63
    @58
    @18
    vw
    @34
    wreu
    #
    wa
    #
    vv
    @34
    wral
    #
    @42
    @67
    cA
    cC
    cpr
    #
    cE
    wcel
    #
    cA
    @16
    cpr
    #
    cE
    wcel
    #
    vw
    @34
    wreu
    #
    wa
    #
    @37
    cB
    @16
    cpr
    #
    cE
    wcel
    #
    vw
    @34
    wreu
    #
    wa
    #
    wa
    #
    @42
    @73
    @77
    @42
    @69
    @72
    @40
    @69
    @33
    @39
    @35
    @69
    @37
    @39
    @69
    @38
    @68
    cE
    cC
    cA
    prcom
    eleq1i
    biimpi
    3ad2ant3
    adantl
    @33
    @0
    @1
    @4
    w3a
    #
    @9
    @32
    wa
    #
    wa
    #
    @35
    @72
    @40
    @33
    @79
    @80
    @33
    @0
    @1
    @4
    @0
    @1
    @2
    @7
    @9
    @32
    simpl11
    #
    @0
    @1
    @2
    @7
    @9
    @32
    simpl12
    #
    @10
    @4
    @32
    @7
    @3
    @4
    @9
    @4
    @5
    @6
    simp1
    3ad2ant2
    adantr
    3jca
    @10
    @9
    @32
    @3
    @7
    @9
    simp3
    #
    anim1i
    jca
    @35
    @37
    @39
    simp1
    @81
    @35
    @72
    vw
    cA
    cB
    cC
    cE
    cG
    cV
    cX
    cY
    3vfriswmgr.v
    3vfriswmgr.e
    3vfriswmgrlem
    imp
    syl2an
    jca
    @42
    @37
    @76
    @33
    @35
    @37
    @39
    simpr2
    @33
    @1
    @0
    cB
    cA
    wne
    #
    w3a
    #
    cV
    cB
    cA
    cC
    ctp
    #
    wceq
    #
    @32
    wa
    #
    wa
    #
    cB
    cA
    cpr
    #
    cE
    wcel
    #
    @76
    @40
    @33
    @86
    @89
    @33
    @1
    @0
    @85
    @83
    @82
    @10
    @85
    @32
    @7
    @3
    @85
    @9
    @4
    @5
    @85
    @6
    @4
    @85
    cA
    cB
    necom
    biimpi
    3ad2ant1
    3ad2ant2
    adantr
    3jca
    @10
    @88
    @32
    @10
    cV
    @8
    @87
    @84
    cA
    cB
    cC
    tpcoma
    syl6eq
    anim1i
    jca
    @35
    @37
    @92
    @39
    @35
    @92
    @34
    @91
    cE
    cA
    cB
    prcom
    #
    eleq1i
    biimpi
    3ad2ant1
    @90
    @92
    wa
    @75
    vw
    @91
    wreu
    #
    @76
    @90
    @92
    @94
    vw
    cB
    cA
    cC
    cE
    cG
    cV
    cY
    cX
    3vfriswmgr.v
    3vfriswmgr.e
    3vfriswmgrlem
    imp
    @34
    @91
    wceq
    @76
    @94
    wb
    @93
    @75
    vw
    @34
    @91
    reueq1
    ax-mp
    sylibr
    syl2an
    jca
    jca
    @33
    @67
    @78
    wb
    #
    @40
    @10
    @95
    @32
    @3
    @7
    @95
    @9
    @0
    @1
    @95
    @2
    @66
    @73
    @77
    vv
    cA
    cB
    cX
    cY
    @12
    cA
    wceq
    #
    @58
    @69
    @65
    @72
    @96
    @57
    @68
    cE
    @12
    cA
    cC
    preq1
    eleq1d
    @96
    @18
    @71
    vw
    @34
    @96
    @17
    @70
    cE
    @12
    cA
    @16
    preq1
    eleq1d
    reubidv
    anbi12d
    @12
    cB
    wceq
    #
    @58
    @37
    @65
    @76
    @97
    @57
    @36
    cE
    @12
    cB
    cC
    preq1
    eleq1d
    @97
    @18
    @75
    vw
    @34
    @97
    @17
    @74
    cE
    @12
    cB
    @16
    preq1
    eleq1d
    reubidv
    anbi12d
    ralprg
    3adant3
    3ad2ant1
    adantr
    adantr
    mpbird
    @33
    @63
    @67
    wb
    #
    @40
    @10
    @98
    @32
    @7
    @3
    @98
    @9
    @7
    @62
    @66
    vv
    @60
    @34
    @5
    @6
    @60
    @34
    wceq
    #
    @4
    cA
    cB
    cC
    diftpsn3
    3adant1
    #
    @7
    @61
    @65
    @58
    @7
    @99
    @61
    @65
    wb
    @100
    @18
    vw
    @60
    @34
    reueq1
    syl
    anbi2d
    raleqbidv
    3ad2ant2
    adantr
    adantr
    mpbird
    3mix3d
    @33
    @30
    @64
    wb
    #
    @40
    @10
    @101
    @32
    @3
    @7
    @101
    @9
    @29
    @49
    @56
    @63
    vh
    cA
    cB
    cC
    cX
    cY
    cZ
    @13
    cA
    wceq
    #
    @28
    @48
    vv
    @26
    @46
    @102
    @19
    @45
    @8
    @13
    cA
    sneq
    difeq2d
    #
    @102
    @15
    @44
    @27
    @47
    @102
    @14
    @43
    cE
    @13
    cA
    @12
    preq2
    eleq1d
    @102
    @26
    @46
    wceq
    @27
    @47
    wb
    @103
    @18
    vw
    @26
    @46
    reueq1
    syl
    anbi12d
    raleqbidv
    @13
    cB
    wceq
    #
    @28
    @55
    vv
    @26
    @53
    @104
    @19
    @52
    @8
    @13
    cB
    sneq
    difeq2d
    #
    @104
    @15
    @51
    @27
    @54
    @104
    @14
    @50
    cE
    @13
    cB
    @12
    preq2
    eleq1d
    @104
    @26
    @53
    wceq
    @27
    @54
    wb
    @105
    @18
    vw
    @26
    @53
    reueq1
    syl
    anbi12d
    raleqbidv
    @13
    cC
    wceq
    #
    @28
    @62
    vv
    @26
    @60
    @106
    @19
    @59
    @8
    @13
    cC
    sneq
    difeq2d
    #
    @106
    @15
    @58
    @27
    @61
    @106
    @14
    @57
    cE
    @13
    cC
    @12
    preq2
    eleq1d
    @106
    @26
    @60
    wceq
    @27
    @61
    wb
    @107
    @18
    vw
    @26
    @60
    reueq1
    syl
    anbi12d
    raleqbidv
    rextpg
    3ad2ant1
    adantr
    adantr
    mpbird
    ex
    sylbid
    expcom
    com23
    mpcom
    com12
    @9
    @3
    @25
    @31
    wb
    @7
    @9
    @24
    @30
    @11
    @23
    @29
    vh
    cV
    @8
    @9
    @22
    @28
    vv
    @20
    @26
    cV
    @8
    @19
    difeq1
    #
    @9
    @21
    @27
    @15
    @9
    @20
    @26
    wceq
    @21
    @27
    wb
    @108
    @18
    vw
    @20
    @26
    reueq1
    syl
    anbi2d
    raleqbidv
    rexeqbi1dv
    imbi2d
    3ad2ant3
    mpbird
end
