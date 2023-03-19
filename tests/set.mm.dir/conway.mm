include "csslt.mm"
include "wbr.mm"
include "cv.mm"
include "csn.mm"
include "wa.mm"
include "csur.mm"
include "crab.mm"
include "c0.mm"
include "wne.mm"
include "wss.mm"
include "cslt.mm"
include "wcel.mm"
include "wi.mm"
include "wral.mm"
include "cbday.mm"
include "cfv.mm"
include "cima.mm"
include "cint.mm"
include "wceq.mm"
include "wreu.mm"
include "wrex.mm"
include "cun.mm"
include "cuni.mm"
include "csuc.mm"
include "w3a.mm"
include "cvv.mm"
include "ssltss1.mm"
include "ssltex1.mm"
include "ssltss2.mm"
include "ssltex2.mm"
include "ssltsep.mm"
include "noeta.mm"
include "syl221anc.mm"
include "3simpa.mm"
include "ad2antrr.mm"
include "snex.mm"
include "jctir.mm"
include "snssi.mm"
include "adantl.mm"
include "adantr.mm"
include "vex.mm"
include "breq2.mm"
include "ralsn.mm"
include "ralbii.mm"
include "biimpri.mm"
include "3jca.mm"
include "brsslt.mm"
include "sylanbrc.mm"
include "ex.mm"
include "jctil.mm"
include "ralcom.mm"
include "breq1.mm"
include "sylbbr.mm"
include "anim12d.mm"
include "syl5.mm"
include "reximdva.mm"
include "mpd.mm"
include "rabn0.mm"
include "sylibr.mm"
include "ssrab2.mm"
include "a1i.mm"
include "simplr3.mm"
include "syl.mm"
include "sselda.mm"
include "simplr1.mm"
include "simplll.mm"
include "r19.21bi.mm"
include "sylib.mm"
include "simprrl.mm"
include "slttrd.mm"
include "ralrimiva.mm"
include "simplr2.mm"
include "simprrr.mm"
include "simplrr.mm"
include "weq.mm"
include "ralbidv.mm"
include "jca32.mm"
include "exp44.mm"
include "ralrimivvva.mm"
include "sneq.mm"
include "breq2d.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "ralrab.mm"
include "elrab.mm"
include "imbi2i.mm"
include "r19.21v.mm"
include "3bitr4i.mm"
include "bitri.mm"
include "nocvxmin.mm"
include "syl3anc.mm"

theorem conway
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vp: setvar p
  let vq: setvar q
  let vr: setvar r

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint A p
  disjoint A q
  disjoint A r
  disjoint p x
  disjoint q x
  disjoint r x
  disjoint p y
  disjoint q y
  disjoint r y
  disjoint p q
  disjoint p r
  disjoint q r
  disjoint B p
  disjoint B q
  disjoint B r
  assert |- ( A <<s B -> E! x e. { y e. No | ( A <<s { y } /\ { y } <<s B ) } ( bday ` x ) = |^| ( bday " { y e. No | ( A <<s { y } /\ { y } <<s B ) } ) )

  proof
    cA
    cB
    csslt
    wbr
    #
    cA
    vy
    cv
    #
    csn
    #
    csslt
    wbr
    #
    @2
    cB
    csslt
    wbr
    #
    wa
    #
    vy
    csur
    crab
    #
    c0
    wne
    #
    @6
    csur
    wss
    #
    vp
    cv
    #
    vr
    cv
    #
    cslt
    wbr
    #
    @10
    vq
    cv
    #
    cslt
    wbr
    #
    wa
    #
    @10
    @6
    wcel
    #
    wi
    #
    vr
    csur
    wral
    #
    vq
    @6
    wral
    #
    vp
    @6
    wral
    #
    vx
    cv
    #
    cbday
    cfv
    cbday
    @6
    cima
    cint
    wceq
    vx
    @6
    wreu
    @0
    @5
    vy
    csur
    wrex
    #
    @7
    @0
    @9
    @1
    cslt
    wbr
    #
    vp
    cA
    wral
    #
    @1
    @12
    cslt
    wbr
    #
    vq
    cB
    wral
    #
    @1
    cbday
    cfv
    cbday
    cA
    cB
    cun
    cima
    cuni
    csuc
    wss
    #
    w3a
    #
    vy
    csur
    wrex
    #
    @21
    @0
    cA
    csur
    wss
    #
    cA
    cvv
    wcel
    #
    cB
    csur
    wss
    #
    cB
    cvv
    wcel
    #
    @9
    @12
    cslt
    wbr
    #
    vq
    cB
    wral
    #
    vp
    cA
    wral
    @28
    cA
    cB
    ssltss1
    #
    cA
    cB
    ssltex1
    #
    cA
    cB
    ssltss2
    #
    cA
    cB
    ssltex2
    #
    vp
    vq
    cA
    cB
    ssltsep
    vp
    vq
    vy
    cA
    cB
    cvv
    cvv
    noeta
    syl221anc
    @0
    @27
    @5
    vy
    csur
    @27
    @23
    @25
    wa
    @0
    @1
    csur
    wcel
    #
    wa
    #
    @5
    @23
    @25
    @26
    3simpa
    @40
    @23
    @3
    @25
    @4
    @40
    @23
    @3
    @40
    @23
    wa
    #
    @30
    @2
    cvv
    wcel
    #
    wa
    @29
    @2
    csur
    wss
    #
    @33
    vq
    @2
    wral
    #
    vp
    cA
    wral
    #
    w3a
    @3
    @41
    @30
    @42
    @0
    @30
    @39
    @23
    @36
    ad2antrr
    @1
    snex
    #
    jctir
    @41
    @29
    @43
    @45
    @0
    @29
    @39
    @23
    @35
    ad2antrr
    @40
    @43
    @23
    @39
    @43
    @0
    @1
    csur
    snssi
    adantl
    #
    adantr
    @23
    @45
    @40
    @45
    @23
    @44
    @22
    vp
    cA
    @33
    @22
    vq
    @1
    vy
    vex
    #
    @12
    @1
    @9
    cslt
    breq2
    ralsn
    ralbii
    biimpri
    adantl
    3jca
    vp
    vq
    cA
    @2
    brsslt
    sylanbrc
    ex
    @40
    @25
    @4
    @40
    @25
    wa
    #
    @42
    @32
    wa
    @43
    @31
    @34
    vp
    @2
    wral
    #
    w3a
    @4
    @49
    @32
    @42
    @0
    @32
    @39
    @25
    @38
    ad2antrr
    @46
    jctil
    @49
    @43
    @31
    @50
    @40
    @43
    @25
    @47
    adantr
    @0
    @31
    @39
    @25
    @37
    ad2antrr
    @25
    @50
    @40
    @50
    @33
    vp
    @2
    wral
    #
    vq
    cB
    wral
    @25
    @33
    vp
    vq
    @2
    cB
    ralcom
    @51
    @24
    vq
    cB
    @33
    @24
    vp
    @1
    @48
    @9
    @1
    @12
    cslt
    breq1
    ralsn
    ralbii
    sylbbr
    adantl
    3jca
    vp
    vq
    @2
    cB
    brsslt
    sylanbrc
    ex
    anim12d
    syl5
    reximdva
    mpd
    @5
    vy
    csur
    rabn0
    sylibr
    @8
    @0
    @5
    vy
    csur
    ssrab2
    a1i
    @0
    cA
    @9
    csn
    #
    csslt
    wbr
    #
    @52
    cB
    csslt
    wbr
    #
    wa
    #
    cA
    @12
    csn
    #
    csslt
    wbr
    #
    @56
    cB
    csslt
    wbr
    #
    wa
    #
    @14
    @10
    csur
    wcel
    #
    cA
    @10
    csn
    #
    csslt
    wbr
    #
    @61
    cB
    csslt
    wbr
    #
    wa
    #
    wa
    #
    wi
    #
    wi
    #
    wi
    #
    vr
    csur
    wral
    #
    vq
    csur
    wral
    #
    vp
    csur
    wral
    #
    @19
    @0
    @68
    vp
    vq
    vr
    csur
    csur
    csur
    @0
    @9
    csur
    wcel
    #
    @12
    csur
    wcel
    #
    @60
    w3a
    #
    wa
    #
    @55
    @59
    @14
    @65
    @75
    @55
    @59
    wa
    #
    @14
    wa
    #
    wa
    #
    @60
    @62
    @63
    @72
    @73
    @60
    @0
    @77
    simplr3
    #
    @78
    @30
    @61
    cvv
    wcel
    #
    wa
    @29
    @61
    csur
    wss
    #
    @20
    @1
    cslt
    wbr
    #
    vy
    @61
    wral
    #
    vx
    cA
    wral
    #
    w3a
    @62
    @78
    @30
    @80
    @0
    @30
    @74
    @77
    @36
    ad2antrr
    @10
    snex
    #
    jctir
    @78
    @29
    @81
    @84
    @0
    @29
    @74
    @77
    @35
    ad2antrr
    #
    @78
    @60
    @81
    @79
    @10
    csur
    snssi
    syl
    #
    @78
    @83
    vx
    cA
    @78
    @20
    cA
    wcel
    #
    wa
    #
    @20
    @10
    cslt
    wbr
    #
    @83
    @89
    @20
    @9
    @10
    @78
    cA
    csur
    @20
    @86
    sselda
    @78
    @72
    @88
    @72
    @73
    @60
    @0
    @77
    simplr1
    adantr
    @78
    @60
    @88
    @79
    adantr
    @89
    @82
    vy
    @52
    wral
    #
    @20
    @9
    cslt
    wbr
    #
    @78
    @91
    vx
    cA
    @78
    @53
    @91
    vx
    cA
    wral
    @77
    @53
    @75
    @53
    @54
    @59
    @14
    simplll
    adantl
    vx
    vy
    cA
    @52
    ssltsep
    syl
    r19.21bi
    @82
    @92
    vy
    @9
    vp
    vex
    @1
    @9
    @20
    cslt
    breq2
    ralsn
    sylib
    @78
    @11
    @88
    @75
    @76
    @11
    @13
    simprrl
    adantr
    slttrd
    @82
    @90
    vy
    @10
    vr
    vex
    #
    @1
    @10
    @20
    cslt
    breq2
    ralsn
    sylibr
    ralrimiva
    3jca
    vx
    vy
    cA
    @61
    brsslt
    sylanbrc
    @78
    @80
    @32
    wa
    @81
    @31
    @82
    vy
    cB
    wral
    #
    vx
    @61
    wral
    #
    w3a
    @63
    @78
    @32
    @80
    @0
    @32
    @74
    @77
    @38
    ad2antrr
    @85
    jctil
    @78
    @81
    @31
    @95
    @87
    @0
    @31
    @74
    @77
    @37
    ad2antrr
    #
    @78
    @10
    @1
    cslt
    wbr
    #
    vy
    cB
    wral
    #
    @95
    @78
    @97
    vy
    cB
    @78
    @1
    cB
    wcel
    #
    wa
    @10
    @12
    @1
    @78
    @60
    @99
    @79
    adantr
    @78
    @73
    @99
    @72
    @73
    @60
    @0
    @77
    simplr2
    adantr
    @78
    cB
    csur
    @1
    @96
    sselda
    @78
    @13
    @99
    @75
    @76
    @11
    @13
    simprrr
    adantr
    @78
    @12
    @1
    cslt
    wbr
    #
    vy
    cB
    @78
    @94
    vx
    @56
    wral
    #
    @100
    vy
    cB
    wral
    #
    @78
    @58
    @101
    @77
    @58
    @75
    @55
    @57
    @58
    @14
    simplrr
    adantl
    vx
    vy
    @56
    cB
    ssltsep
    syl
    @94
    @102
    vx
    @12
    vq
    vex
    vx
    vq
    weq
    @82
    @100
    vy
    cB
    @20
    @12
    @1
    cslt
    breq1
    ralbidv
    ralsn
    sylib
    r19.21bi
    slttrd
    ralrimiva
    @94
    @98
    vx
    @10
    @93
    vx
    vr
    weq
    @82
    @97
    vy
    cB
    @20
    @10
    @1
    cslt
    breq1
    ralbidv
    ralsn
    sylibr
    3jca
    vx
    vy
    @61
    cB
    brsslt
    sylanbrc
    jca32
    exp44
    ralrimivvva
    @67
    vr
    csur
    wral
    #
    vq
    csur
    wral
    #
    vp
    @6
    wral
    @55
    @104
    wi
    #
    vp
    csur
    wral
    @19
    @71
    @5
    @55
    @104
    vp
    vy
    csur
    vy
    vp
    weq
    #
    @3
    @53
    @4
    @54
    @106
    @2
    @52
    cA
    csslt
    @1
    @9
    sneq
    #
    breq2d
    @106
    @2
    @52
    cB
    csslt
    @107
    breq1d
    anbi12d
    ralrab
    @18
    @104
    vp
    @6
    @66
    vr
    csur
    wral
    #
    vq
    @6
    wral
    @59
    @108
    wi
    #
    vq
    csur
    wral
    @18
    @104
    @5
    @59
    @108
    vq
    vy
    csur
    vy
    vq
    weq
    #
    @3
    @57
    @4
    @58
    @110
    @2
    @56
    cA
    csslt
    @1
    @12
    sneq
    #
    breq2d
    @110
    @2
    @56
    cB
    csslt
    @111
    breq1d
    anbi12d
    ralrab
    @17
    @108
    vq
    @6
    @16
    @66
    vr
    csur
    @15
    @65
    @14
    @5
    @64
    vy
    @10
    csur
    vy
    vr
    weq
    #
    @3
    @62
    @4
    @63
    @112
    @2
    @61
    cA
    csslt
    @1
    @10
    sneq
    #
    breq2d
    @112
    @2
    @61
    cB
    csslt
    @113
    breq1d
    anbi12d
    elrab
    imbi2i
    ralbii
    ralbii
    @103
    @109
    vq
    csur
    @59
    @66
    vr
    csur
    r19.21v
    ralbii
    3bitr4i
    ralbii
    @70
    @105
    vp
    csur
    @70
    @55
    @103
    wi
    #
    vq
    csur
    wral
    @105
    @69
    @114
    vq
    csur
    @55
    @67
    vr
    csur
    r19.21v
    ralbii
    @55
    @103
    vq
    csur
    r19.21v
    bitri
    ralbii
    3bitr4i
    sylibr
    vp
    vq
    vr
    vx
    @6
    nocvxmin
    syl3anc
end
