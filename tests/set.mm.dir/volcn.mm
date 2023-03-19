include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
include "wf.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "ccncf.mm"
include "cicc.mm"
include "cin.mm"
include "covol.mm"
include "wceq.mm"
include "simpll.mm"
include "iccmbl.mm"
include "adantll.mm"
include "inmbl.mm"
include "syl2anc.mm"
include "mblvol.mm"
include "syl.mm"
include "wss.mm"
include "inss2.mm"
include "a1i.mm"
include "mblss.mm"
include "iccvolcl.mm"
include "eqeltrrd.mm"
include "ovolsscl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "fmptd.mm"
include "simprr.mm"
include "weq.mm"
include "oveq12.mm"
include "ancoms.mm"
include "fveq2d.mm"
include "breq1d.mm"
include "fveq2.mm"
include "oveqan12rd.mm"
include "imbi12d.mm"
include "ssid.mm"
include "cc.mm"
include "recn.mm"
include "abssub.mm"
include "syl2anr.mm"
include "adantl.mm"
include "adantr.mm"
include "ffvelrn.mm"
include "anim12dan.mm"
include "sylan.mm"
include "cle.mm"
include "w3a.mm"
include "simpr2.mm"
include "oveq2.mm"
include "ineq2d.mm"
include "fvex.mm"
include "fvmpt.mm"
include "simplll.mm"
include "simplr.mm"
include "eqtrd.mm"
include "simpr1.mm"
include "simp1.mm"
include "syl2an.mm"
include "oveq12d.mm"
include "caddc.mm"
include "cun.mm"
include "ffvelrnd.mm"
include "leidd.mm"
include "simpr3.mm"
include "iccss.mm"
include "syl22anc.mm"
include "sslin.mm"
include "sstrd.mm"
include "iccssre.mm"
include "unssd.mm"
include "resubcld.mm"
include "readdcld.mm"
include "ovolicc.mm"
include "ovolun.mm"
include "oveq2d.mm"
include "breqtrd.mm"
include "ovollecl.mm"
include "simpr.mm"
include "wb.mm"
include "simp2.mm"
include "elicc2.mm"
include "mpbir3and.mm"
include "iccsplit.mm"
include "eqimss.mm"
include "ssun4.mm"
include "lecasei.mm"
include "indi.mm"
include "unss2.mm"
include "ax-mp.mm"
include "eqsstri.mm"
include "syl6ss.mm"
include "ovolss.mm"
include "letrd.mm"
include "lesubadd2d.mm"
include "mpbird.mm"
include "eqbrtrd.mm"
include "rpred.mm"
include "lelttr.mm"
include "mpand.mm"
include "abssubge0.mm"
include "3brtr4d.mm"
include "abssubge0d.mm"
include "3imtr4d.mm"
include "wlogle.mm"
include "anassrs.mm"
include "ralrimiva.mm"
include "anasss.mm"
include "ancom2s.mm"
include "breq2.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "ralrimivva.mm"
include "ax-resscn.mm"
include "elcncf2.mm"
include "mp2an.mm"
include "sylanbrc.mm"

theorem volcn
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let ve: setvar e
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vz: setvar z
  let vd: setvar d
  assume volcn.1: |- F = ( x e. RR |-> ( vol ` ( A i^i ( B [,] x ) ) ) )

  disjoint A x
  disjoint B x
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint A e
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B e
  disjoint B u
  disjoint B v
  disjoint B y
  disjoint B z
  disjoint d e
  disjoint d u
  disjoint d v
  disjoint d y
  disjoint d z
  disjoint F d
  disjoint F e
  disjoint F u
  disjoint F v
  disjoint F y
  disjoint F z
  assert |- ( ( A e. dom vol /\ B e. RR ) -> F e. ( RR -cn-> RR ) )

  proof
    cA
    cvol
    cdm
    #
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cr
    cr
    cF
    wf
    #
    vz
    cv
    #
    vy
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    vd
    cv
    #
    clt
    wbr
    #
    @5
    cF
    cfv
    #
    @6
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vz
    cr
    wral
    #
    vd
    crp
    wrex
    #
    ve
    crp
    wral
    vy
    cr
    wral
    #
    cF
    cr
    cr
    ccncf
    co
    wcel
    #
    @3
    vx
    cr
    cA
    cB
    vx
    cv
    #
    cicc
    co
    #
    cin
    #
    cvol
    cfv
    #
    cr
    cF
    @3
    @22
    cr
    wcel
    #
    wa
    #
    @25
    @24
    covol
    cfv
    #
    cr
    @27
    @24
    @0
    wcel
    #
    @25
    @28
    wceq
    @27
    @1
    @23
    @0
    wcel
    #
    @29
    @1
    @2
    @26
    simpll
    @2
    @26
    @30
    @1
    cB
    @22
    iccmbl
    adantll
    #
    cA
    @23
    inmbl
    syl2anc
    @24
    mblvol
    syl
    @27
    @24
    @23
    wss
    #
    @23
    cr
    wss
    #
    @23
    covol
    cfv
    #
    cr
    wcel
    @28
    cr
    wcel
    @32
    @27
    cA
    @23
    inss2
    a1i
    @27
    @30
    @33
    @31
    @23
    mblss
    syl
    @27
    @23
    cvol
    cfv
    #
    @34
    cr
    @27
    @30
    @35
    @34
    wceq
    @31
    @23
    mblvol
    syl
    @2
    @26
    @35
    cr
    wcel
    @1
    cB
    @22
    iccvolcl
    adantll
    eqeltrrd
    @24
    @23
    ovolsscl
    syl3anc
    eqeltrd
    volcn.1
    fmptd
    #
    @3
    @19
    vy
    ve
    cr
    crp
    @3
    @6
    cr
    wcel
    #
    @15
    crp
    wcel
    #
    wa
    wa
    @38
    @8
    @15
    clt
    wbr
    #
    @16
    wi
    #
    vz
    cr
    wral
    #
    @19
    @3
    @37
    @38
    simprr
    @3
    @38
    @37
    @41
    @3
    @38
    @37
    @41
    @3
    @38
    wa
    #
    @37
    wa
    @40
    vz
    cr
    @42
    @37
    @5
    cr
    wcel
    #
    @40
    @42
    vv
    cv
    #
    vu
    cv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    @44
    cF
    cfv
    #
    @45
    cF
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    wi
    @40
    @6
    @5
    cmin
    co
    #
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    @12
    @11
    cmin
    co
    #
    cabs
    cfv
    #
    @15
    clt
    wbr
    #
    wi
    vy
    vz
    vu
    vv
    cr
    vu
    vy
    weq
    #
    vv
    vz
    weq
    #
    wa
    #
    @48
    @39
    @53
    @16
    @62
    @47
    @8
    @15
    clt
    @62
    @46
    @7
    cabs
    @61
    @60
    @46
    @7
    wceq
    @44
    @5
    @45
    @6
    cmin
    oveq12
    ancoms
    fveq2d
    breq1d
    @62
    @52
    @14
    @15
    clt
    @62
    @51
    @13
    cabs
    @61
    @60
    @49
    @11
    @50
    @12
    cmin
    @44
    @5
    cF
    fveq2
    @45
    @6
    cF
    fveq2
    oveqan12rd
    fveq2d
    breq1d
    imbi12d
    vu
    vz
    weq
    #
    vv
    vy
    weq
    #
    wa
    #
    @48
    @56
    @53
    @59
    @65
    @47
    @55
    @15
    clt
    @65
    @46
    @54
    cabs
    @64
    @63
    @46
    @54
    wceq
    @44
    @6
    @45
    @5
    cmin
    oveq12
    ancoms
    fveq2d
    breq1d
    @65
    @52
    @58
    @15
    clt
    @65
    @51
    @57
    cabs
    @64
    @63
    @49
    @12
    @50
    @11
    cmin
    @44
    @6
    cF
    fveq2
    @45
    @5
    cF
    fveq2
    oveqan12rd
    fveq2d
    breq1d
    imbi12d
    cr
    cr
    wss
    @42
    cr
    ssid
    a1i
    @42
    @37
    @43
    wa
    #
    wa
    #
    @39
    @56
    @16
    @59
    @67
    @8
    @55
    @15
    clt
    @66
    @8
    @55
    wceq
    #
    @42
    @43
    @5
    cc
    wcel
    @6
    cc
    wcel
    @68
    @37
    @5
    recn
    @6
    recn
    @5
    @6
    abssub
    syl2anr
    adantl
    breq1d
    @67
    @14
    @58
    @15
    clt
    @67
    @12
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    wa
    #
    @14
    @58
    wceq
    #
    @42
    @4
    @66
    @71
    @3
    @4
    @38
    @36
    adantr
    #
    @4
    @37
    @69
    @43
    @70
    cr
    cr
    @6
    cF
    ffvelrn
    cr
    cr
    @5
    cF
    ffvelrn
    anim12dan
    sylan
    @70
    @11
    cc
    wcel
    @12
    cc
    wcel
    @72
    @69
    @11
    recn
    @12
    recn
    @11
    @12
    abssub
    syl2anr
    syl
    breq1d
    imbi12d
    @42
    @37
    @43
    @6
    @5
    cle
    wbr
    #
    w3a
    #
    wa
    #
    @7
    @15
    clt
    wbr
    #
    @13
    @15
    clt
    wbr
    #
    @39
    @16
    @76
    @13
    @7
    cle
    wbr
    #
    @77
    @78
    @76
    @13
    cA
    cB
    @5
    cicc
    co
    #
    cin
    #
    covol
    cfv
    #
    cA
    cB
    @6
    cicc
    co
    #
    cin
    #
    covol
    cfv
    #
    cmin
    co
    #
    @7
    cle
    @76
    @11
    @82
    @12
    @85
    cmin
    @76
    @11
    @81
    cvol
    cfv
    #
    @82
    @76
    @43
    @11
    @87
    wceq
    @42
    @37
    @43
    @74
    simpr2
    #
    vx
    @5
    @25
    @87
    cr
    cF
    vx
    vz
    weq
    #
    @24
    @81
    cvol
    @89
    @23
    @80
    cA
    @22
    @5
    cB
    cicc
    oveq2
    ineq2d
    fveq2d
    volcn.1
    @81
    cvol
    fvex
    fvmpt
    syl
    @76
    @81
    @0
    wcel
    #
    @87
    @82
    wceq
    @76
    @1
    @80
    @0
    wcel
    #
    @90
    @1
    @2
    @38
    @75
    simplll
    #
    @76
    @2
    @43
    @91
    @42
    @2
    @75
    @1
    @2
    @38
    simplr
    #
    adantr
    #
    @88
    cB
    @5
    iccmbl
    syl2anc
    cA
    @80
    inmbl
    syl2anc
    #
    @81
    mblvol
    syl
    eqtrd
    #
    @76
    @12
    @84
    cvol
    cfv
    #
    @85
    @76
    @37
    @12
    @97
    wceq
    @42
    @37
    @43
    @74
    simpr1
    #
    vx
    @6
    @25
    @97
    cr
    cF
    vx
    vy
    weq
    #
    @24
    @84
    cvol
    @99
    @23
    @83
    cA
    @22
    @6
    cB
    cicc
    oveq2
    ineq2d
    fveq2d
    volcn.1
    @84
    cvol
    fvex
    fvmpt
    syl
    @76
    @84
    @0
    wcel
    #
    @97
    @85
    wceq
    @76
    @1
    @83
    @0
    wcel
    #
    @100
    @92
    @42
    @2
    @37
    @101
    @75
    @93
    @37
    @43
    @74
    simp1
    cB
    @6
    iccmbl
    syl2an
    cA
    @83
    inmbl
    syl2anc
    @84
    mblvol
    syl
    eqtrd
    #
    oveq12d
    @76
    @86
    @7
    cle
    wbr
    @82
    @85
    @7
    caddc
    co
    #
    cle
    wbr
    @76
    @82
    @84
    @6
    @5
    cicc
    co
    #
    cun
    #
    covol
    cfv
    #
    @103
    @76
    @11
    @82
    cr
    @96
    @76
    cr
    cr
    @5
    cF
    @42
    @4
    @75
    @73
    adantr
    #
    @88
    ffvelrnd
    #
    eqeltrrd
    #
    @76
    @105
    cr
    wss
    #
    @103
    cr
    wcel
    @106
    @103
    cle
    wbr
    @106
    cr
    wcel
    @76
    @84
    @104
    cr
    @76
    @84
    @81
    cr
    @76
    @83
    @80
    wss
    #
    @84
    @81
    wss
    #
    @76
    @2
    @43
    cB
    cB
    cle
    wbr
    @74
    @111
    @94
    @88
    @76
    cB
    @94
    leidd
    @42
    @37
    @43
    @74
    simpr3
    #
    cB
    @5
    cB
    @6
    iccss
    syl22anc
    @83
    @80
    cA
    sslin
    syl
    #
    @76
    @90
    @81
    cr
    wss
    #
    @95
    @81
    mblss
    syl
    #
    sstrd
    #
    @76
    @37
    @43
    @104
    cr
    wss
    #
    @98
    @88
    @6
    @5
    iccssre
    syl2anc
    #
    unssd
    #
    @76
    @85
    @7
    @76
    @12
    @85
    cr
    @102
    @76
    cr
    cr
    @6
    cF
    @107
    @98
    ffvelrnd
    #
    eqeltrrd
    #
    @76
    @5
    @6
    @88
    @98
    resubcld
    #
    readdcld
    #
    @76
    @106
    @85
    @104
    covol
    cfv
    #
    caddc
    co
    #
    @103
    cle
    @76
    @84
    cr
    wss
    @85
    cr
    wcel
    @118
    @125
    cr
    wcel
    @106
    @126
    cle
    wbr
    @117
    @122
    @119
    @76
    @125
    @7
    cr
    @75
    @125
    @7
    wceq
    @42
    @6
    @5
    ovolicc
    adantl
    #
    @123
    eqeltrd
    @84
    @104
    ovolun
    syl22anc
    @76
    @125
    @7
    @85
    caddc
    @127
    oveq2d
    breqtrd
    #
    @105
    @103
    ovollecl
    syl3anc
    @124
    @76
    @81
    @105
    wss
    @110
    @82
    @106
    cle
    wbr
    @76
    @81
    cA
    @83
    @104
    cun
    #
    cin
    #
    @105
    @76
    @80
    @129
    wss
    #
    @81
    @130
    wss
    @76
    @131
    cB
    @6
    @94
    @98
    @76
    cB
    @6
    cle
    wbr
    #
    wa
    #
    @80
    @129
    wceq
    #
    @131
    @133
    @2
    @43
    @6
    @80
    wcel
    #
    @134
    @76
    @2
    @132
    @94
    adantr
    @76
    @43
    @132
    @88
    adantr
    @133
    @135
    @37
    @132
    @74
    @76
    @37
    @132
    @98
    adantr
    @76
    @132
    simpr
    @76
    @74
    @132
    @113
    adantr
    @76
    @135
    @37
    @132
    @74
    w3a
    wb
    #
    @132
    @42
    @2
    @43
    @136
    @75
    @93
    @37
    @43
    @74
    simp2
    cB
    @5
    @6
    elicc2
    syl2an
    adantr
    mpbir3and
    cB
    @5
    @6
    iccsplit
    syl3anc
    @80
    @129
    eqimss
    syl
    @76
    @6
    cB
    cle
    wbr
    #
    wa
    #
    @80
    @104
    wss
    #
    @131
    @138
    @37
    @43
    @137
    @5
    @5
    cle
    wbr
    @139
    @76
    @37
    @137
    @98
    adantr
    @76
    @43
    @137
    @88
    adantr
    #
    @76
    @137
    simpr
    @138
    @5
    @140
    leidd
    @6
    @5
    cB
    @5
    iccss
    syl22anc
    @80
    @104
    @83
    ssun4
    syl
    lecasei
    @80
    @129
    cA
    sslin
    syl
    @130
    @84
    cA
    @104
    cin
    #
    cun
    #
    @105
    cA
    @83
    @104
    indi
    @141
    @104
    wss
    @142
    @105
    wss
    cA
    @104
    inss2
    @141
    @104
    @84
    unss2
    ax-mp
    eqsstri
    syl6ss
    @120
    @81
    @105
    ovolss
    syl2anc
    @128
    letrd
    @76
    @82
    @85
    @7
    @109
    @122
    @123
    lesubadd2d
    mpbird
    eqbrtrd
    @76
    @13
    cr
    wcel
    @7
    cr
    wcel
    @15
    cr
    wcel
    @79
    @77
    wa
    @78
    wi
    @76
    @11
    @12
    @108
    @121
    resubcld
    @123
    @76
    @15
    @3
    @38
    @75
    simplr
    rpred
    @13
    @7
    @15
    lelttr
    syl3anc
    mpand
    @76
    @8
    @7
    @15
    clt
    @75
    @8
    @7
    wceq
    @42
    @6
    @5
    abssubge0
    adantl
    breq1d
    @76
    @14
    @13
    @15
    clt
    @76
    @12
    @11
    @121
    @108
    @76
    @85
    @82
    @12
    @11
    cle
    @76
    @112
    @115
    @85
    @82
    cle
    wbr
    @114
    @116
    @84
    @81
    ovolss
    syl2anc
    @102
    @96
    3brtr4d
    abssubge0d
    breq1d
    3imtr4d
    wlogle
    anassrs
    ralrimiva
    anasss
    ancom2s
    @18
    @41
    vd
    @15
    crp
    vd
    ve
    weq
    #
    @17
    @40
    vz
    cr
    @143
    @10
    @39
    @16
    @9
    @15
    @8
    clt
    breq2
    imbi1d
    ralbidv
    rspcev
    syl2anc
    ralrimivva
    cr
    cc
    wss
    #
    @144
    @21
    @4
    @20
    wa
    wb
    ax-resscn
    ax-resscn
    vy
    ve
    vd
    vz
    cr
    cr
    cF
    elcncf2
    mp2an
    sylanbrc
end
