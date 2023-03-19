include "ctx.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "c1st.mm"
include "cfv.mm"
include "cv.mm"
include "c2.mm"
include "cdiv.mm"
include "cmin.mm"
include "caddc.mm"
include "cioo.mm"
include "c2nd.mm"
include "cxp.mm"
include "wss.mm"
include "crp.mm"
include "wrex.mm"
include "wral.mm"
include "crn.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cxr.mm"
include "wfn.mm"
include "cpw.mm"
include "wf.mm"
include "clt.mm"
include "df-ioo.mm"
include "ixxf.mm"
include "ffn.mm"
include "mp1i.mm"
include "cr.mm"
include "cuni.mm"
include "elssuni.mm"
include "ctg.mm"
include "ctop.mm"
include "retop.mm"
include "eqeltri.mm"
include "uniretop.mm"
include "unieqi.mm"
include "eqtr4i.mm"
include "txunii.mm"
include "syl6sseqr.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "sseldd.mm"
include "xp1st.mm"
include "syl.mm"
include "simpr.mm"
include "rpred.mm"
include "rehalfcld.mm"
include "resubcld.mm"
include "rexrd.mm"
include "readdcld.mm"
include "fnovrn.mm"
include "syl3anc.mm"
include "xp2nd.mm"
include "eqidd.mm"
include "xpeq1.mm"
include "eqeq2d.mm"
include "xpeq2.mm"
include "rspc2ev.mm"
include "eqid.mm"
include "vex.mm"
include "xpex.mm"
include "elrnmpt2.mm"
include "sylibr.mm"
include "syl6eleqr.mm"
include "ralrimiva.mm"
include "cvv.mm"
include "xpss.mm"
include "sseldi.mm"
include "wbr.mm"
include "rphalfcld.mm"
include "ltsubrpd.mm"
include "ltaddrpd.mm"
include "w3a.mm"
include "wb.mm"
include "elioo1.mm"
include "syl2anc.mm"
include "mpbir3and.mm"
include "jca.mm"
include "elxp7.mm"
include "sylanbrc.mm"
include "ccnv.mm"
include "cabs.mm"
include "ccom.mm"
include "cbl.mm"
include "cima.mm"
include "cmnf.mm"
include "cpnf.mm"
include "cle.mm"
include "mnfle.mm"
include "pnfge.mm"
include "mnfxr.mm"
include "pnfxr.mm"
include "ioossioo.mm"
include "mpanl12.mm"
include "ioomax.mm"
include "syl6sseq.mm"
include "xpss12.mm"
include "sselda.mm"
include "expcom.mm"
include "ancld.mm"
include "imdistanri.mm"
include "cre.mm"
include "cim.mm"
include "wi.mm"
include "adantr.mm"
include "simpr1.mm"
include "3anassrs.mm"
include "cnre2csqima.mm"
include "cc.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "chmeo.mm"
include "wf1o.mm"
include "cnrehmeo.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "hmeof1o.mm"
include "f1of.mm"
include "mp2b.mm"
include "a1i.mm"
include "ffvelrnd.mm"
include "ffvelrnda.mm"
include "sqsscirc2.mm"
include "syl21anc.mm"
include "imp.mm"
include "cxmt.mm"
include "rpxrd.mm"
include "cnxmet.mm"
include "jctil.mm"
include "cnmetdval.mm"
include "eqbrtrd.mm"
include "elbl3.mm"
include "biimpar.mm"
include "syldan.mm"
include "ex.mm"
include "syld.mm"
include "wfun.mm"
include "cdm.mm"
include "f1ocnv.mm"
include "f1ofun.mm"
include "ax-mp.mm"
include "f1odm.mm"
include "funfvima.mm"
include "sylancr.mm"
include "f1ocnvfv1.mm"
include "eleq1d.mm"
include "biimpd.mm"
include "3syld.mm"
include "ssrdv.mm"
include "ci.mm"
include "cmul.mm"
include "mpt2fun.mm"
include "hmeoima.mm"
include "mpan.mm"
include "cnfldtopn.mm"
include "elmopn2.mm"
include "simprbi.mm"
include "oveq1.mm"
include "sseq1d.mm"
include "rexbidv.mm"
include "rspcva.mm"
include "imass2.mm"
include "wf1.mm"
include "f1of1.mm"
include "f1imacnv.mm"
include "sseq2d.mm"
include "syl5ib.mm"
include "reximdv.mm"
include "mpd.mm"
include "r19.29.mm"
include "sstr.mm"
include "reximi.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "rexlimivw.mm"

theorem tpr2rico
  let vx: setvar x
  let vy: setvar y
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cG: class G
  let cJ: class J
  let cX: class X
  let vr: setvar r
  let vz: setvar z
  let vd: setvar d
  let vm: setvar m
  assume tpr2rico.0: |- J = ( topGen ` ran (,) )
  assume tpr2rico.1: |- G = ( u e. RR , v e. RR |-> ( u + ( _i x. v ) ) )
  assume tpr2rico.2: |- B = ran ( x e. ran (,) , y e. ran (,) |-> ( x X. y ) )

  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint r x
  disjoint A r
  disjoint A x
  disjoint B r
  disjoint G x
  disjoint J x
  disjoint X x
  disjoint r y
  disjoint X y
  disjoint X r
  disjoint u z
  disjoint v z
  disjoint x z
  disjoint y z
  disjoint d m
  disjoint d r
  disjoint d x
  disjoint A d
  disjoint m r
  disjoint m x
  disjoint A m
  disjoint B d
  disjoint G d
  disjoint G m
  disjoint J d
  disjoint d y
  disjoint X d
  disjoint m y
  disjoint X m
  assert |- ( ( A e. ( J tX J ) /\ X e. A ) -> E. r e. B ( X e. r /\ r C_ A ) )

  proof
    cA
    cJ
    cJ
    ctx
    co
    #
    wcel
    #
    cX
    cA
    wcel
    #
    wa
    #
    cX
    c1st
    cfv
    #
    vd
    cv
    #
    c2
    cdiv
    co
    #
    cmin
    co
    #
    @4
    @6
    caddc
    co
    #
    cioo
    co
    #
    cX
    c2nd
    cfv
    #
    @6
    cmin
    co
    #
    @10
    @6
    caddc
    co
    #
    cioo
    co
    #
    cxp
    #
    cB
    wcel
    #
    cX
    @14
    wcel
    #
    @14
    cA
    wss
    #
    wa
    #
    wa
    #
    vd
    crp
    wrex
    #
    cX
    vr
    cv
    #
    wcel
    #
    @21
    cA
    wss
    #
    wa
    #
    vr
    cB
    wrex
    #
    @3
    @15
    vd
    crp
    wral
    @18
    vd
    crp
    wrex
    #
    @20
    @3
    @15
    vd
    crp
    @3
    @5
    crp
    wcel
    #
    wa
    #
    @14
    vx
    vy
    cioo
    crn
    #
    @29
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    cB
    @28
    @14
    @32
    wceq
    #
    vy
    @29
    wrex
    vx
    @29
    wrex
    #
    @14
    @34
    wcel
    @28
    @9
    @29
    wcel
    #
    @13
    @29
    wcel
    #
    @14
    @14
    wceq
    #
    @36
    @28
    cioo
    cxr
    cxr
    cxp
    #
    wfn
    #
    @7
    cxr
    wcel
    #
    @8
    cxr
    wcel
    #
    @37
    @40
    cxr
    cpw
    #
    cioo
    wf
    @41
    @28
    vx
    vy
    vz
    clt
    clt
    cioo
    vx
    vy
    vz
    df-ioo
    ixxf
    @40
    @44
    cioo
    ffn
    mp1i
    #
    @28
    @7
    @28
    @4
    @6
    @28
    cX
    cr
    cr
    cxp
    #
    wcel
    #
    @4
    cr
    wcel
    @28
    cA
    @46
    cX
    @1
    cA
    @46
    wss
    #
    @2
    @27
    @1
    cA
    @0
    cuni
    @46
    cA
    @0
    elssuni
    cJ
    cJ
    cr
    cr
    cJ
    @29
    ctg
    cfv
    #
    ctop
    tpr2rico.0
    retop
    eqeltri
    #
    @50
    cr
    @49
    cuni
    cJ
    cuni
    uniretop
    cJ
    @49
    tpr2rico.0
    unieqi
    eqtr4i
    #
    @51
    txunii
    #
    syl6sseqr
    #
    ad2antrr
    @1
    @2
    @27
    simplr
    sseldd
    #
    cX
    cr
    cr
    xp1st
    syl
    #
    @28
    @5
    @28
    @5
    @3
    @27
    simpr
    #
    rpred
    rehalfcld
    #
    resubcld
    rexrd
    #
    @28
    @8
    @28
    @4
    @6
    @55
    @57
    readdcld
    rexrd
    #
    cxr
    cxr
    @7
    @8
    cioo
    fnovrn
    syl3anc
    @28
    @41
    @11
    cxr
    wcel
    #
    @12
    cxr
    wcel
    #
    @38
    @45
    @28
    @11
    @28
    @10
    @6
    @28
    @47
    @10
    cr
    wcel
    @54
    cX
    cr
    cr
    xp2nd
    syl
    #
    @57
    resubcld
    rexrd
    #
    @28
    @12
    @28
    @10
    @6
    @62
    @57
    readdcld
    rexrd
    #
    cxr
    cxr
    @11
    @12
    cioo
    fnovrn
    syl3anc
    @28
    @14
    eqidd
    @35
    @39
    @14
    @9
    @31
    cxp
    #
    wceq
    vx
    vy
    @9
    @13
    @29
    @29
    @30
    @9
    wceq
    @32
    @65
    @14
    @30
    @9
    @31
    xpeq1
    eqeq2d
    @31
    @13
    wceq
    @65
    @14
    @14
    @31
    @13
    @9
    xpeq2
    eqeq2d
    rspc2ev
    syl3anc
    vx
    vy
    @29
    @29
    @32
    @14
    @33
    @33
    eqid
    @30
    @31
    vx
    vex
    vy
    vex
    xpex
    elrnmpt2
    sylibr
    tpr2rico.2
    syl6eleqr
    ralrimiva
    @3
    @16
    vd
    crp
    wral
    @17
    vd
    crp
    wrex
    #
    @26
    @3
    @16
    vd
    crp
    @28
    cX
    cvv
    cvv
    cxp
    #
    wcel
    @4
    @9
    wcel
    #
    @10
    @13
    wcel
    #
    wa
    @16
    @28
    @46
    @67
    cX
    cr
    cr
    xpss
    @54
    sseldi
    @28
    @68
    @69
    @28
    @68
    @4
    cxr
    wcel
    #
    @7
    @4
    clt
    wbr
    #
    @4
    @8
    clt
    wbr
    #
    @28
    @4
    @55
    rexrd
    @28
    @4
    @6
    @55
    @28
    @5
    @56
    rphalfcld
    #
    ltsubrpd
    @28
    @4
    @6
    @55
    @73
    ltaddrpd
    @28
    @42
    @43
    @68
    @70
    @71
    @72
    w3a
    wb
    @58
    @59
    @7
    @8
    @4
    elioo1
    syl2anc
    mpbir3and
    @28
    @69
    @10
    cxr
    wcel
    #
    @11
    @10
    clt
    wbr
    #
    @10
    @12
    clt
    wbr
    #
    @28
    @10
    @62
    rexrd
    @28
    @10
    @6
    @62
    @73
    ltsubrpd
    @28
    @10
    @6
    @62
    @73
    ltaddrpd
    @28
    @60
    @61
    @69
    @74
    @75
    @76
    w3a
    wb
    @63
    @64
    @11
    @12
    @10
    elioo1
    syl2anc
    mpbir3and
    jca
    cX
    @9
    @13
    elxp7
    sylanbrc
    ralrimiva
    @3
    @14
    cG
    ccnv
    #
    cX
    cG
    cfv
    #
    @5
    cabs
    cmin
    ccom
    #
    cbl
    cfv
    #
    co
    #
    cima
    #
    wss
    #
    @82
    cA
    wss
    #
    wa
    #
    vd
    crp
    wrex
    #
    @66
    @3
    @83
    vd
    crp
    wral
    @84
    vd
    crp
    wrex
    #
    @86
    @3
    @83
    vd
    crp
    @28
    vx
    @14
    @82
    @28
    @30
    @14
    wcel
    #
    @30
    @82
    wcel
    #
    @28
    @88
    wa
    @28
    @30
    @46
    wcel
    #
    wa
    #
    @88
    wa
    @89
    @88
    @28
    @91
    @88
    @28
    @90
    @28
    @88
    @90
    @28
    @14
    @46
    @30
    @28
    @9
    cr
    wss
    @13
    cr
    wss
    @14
    @46
    wss
    @28
    @9
    cmnf
    cpnf
    cioo
    co
    #
    cr
    @28
    cmnf
    @7
    cle
    wbr
    #
    @8
    cpnf
    cle
    wbr
    #
    @9
    @92
    wss
    #
    @28
    @42
    @93
    @58
    @7
    mnfle
    syl
    @28
    @43
    @94
    @59
    @8
    pnfge
    syl
    cmnf
    cxr
    wcel
    #
    cpnf
    cxr
    wcel
    #
    @93
    @94
    wa
    @95
    mnfxr
    pnfxr
    cmnf
    cpnf
    @7
    @8
    ioossioo
    mpanl12
    syl2anc
    ioomax
    syl6sseq
    @28
    @13
    @92
    cr
    @28
    cmnf
    @11
    cle
    wbr
    #
    @12
    cpnf
    cle
    wbr
    #
    @13
    @92
    wss
    #
    @28
    @60
    @98
    @63
    @11
    mnfle
    syl
    @28
    @61
    @99
    @64
    @12
    pnfge
    syl
    @96
    @97
    @98
    @99
    wa
    @100
    mnfxr
    pnfxr
    cmnf
    cpnf
    @11
    @12
    ioossioo
    mpanl12
    syl2anc
    ioomax
    syl6sseq
    @9
    cr
    @13
    cr
    xpss12
    syl2anc
    sselda
    expcom
    ancld
    imdistanri
    @91
    @88
    @89
    @91
    @88
    @30
    cG
    cfv
    #
    @81
    wcel
    #
    @101
    @77
    cfv
    #
    @82
    wcel
    #
    @89
    @91
    @88
    @101
    @78
    cmin
    co
    #
    cre
    cfv
    cabs
    cfv
    @6
    clt
    wbr
    @105
    cim
    cfv
    cabs
    cfv
    @6
    clt
    wbr
    wa
    #
    @102
    @91
    @47
    @90
    @6
    crp
    wcel
    @88
    @106
    wi
    @1
    @2
    @27
    @90
    @47
    @1
    @2
    @27
    @90
    w3a
    #
    wa
    cA
    @46
    cX
    @1
    @48
    @107
    @53
    adantr
    @1
    @2
    @27
    @90
    simpr1
    sseldd
    3anassrs
    #
    @28
    @90
    simpr
    #
    @91
    @5
    @3
    @27
    @90
    simplr
    #
    rphalfcld
    vu
    vv
    @6
    cG
    cX
    @30
    tpr2rico.1
    cnre2csqima
    syl3anc
    @91
    @106
    @102
    @91
    @106
    @105
    cabs
    cfv
    #
    @5
    clt
    wbr
    #
    @102
    @91
    @106
    @112
    @91
    @78
    cc
    wcel
    #
    @101
    cc
    wcel
    #
    @27
    @106
    @112
    wi
    @91
    @46
    cc
    cX
    cG
    @46
    cc
    cG
    wf
    #
    @91
    cG
    @0
    ccnfld
    ctopn
    cfv
    #
    chmeo
    co
    wcel
    #
    @46
    cc
    cG
    wf1o
    #
    @115
    vu
    vv
    cG
    cJ
    @116
    tpr2rico.1
    tpr2rico.0
    @116
    eqid
    #
    cnrehmeo
    #
    cG
    @0
    @116
    @46
    cc
    @52
    cc
    @116
    @116
    @119
    cnfldtopon
    toponunii
    hmeof1o
    #
    @46
    cc
    cG
    f1of
    mp2b
    #
    a1i
    @108
    ffvelrnd
    #
    @28
    @46
    cc
    @30
    cG
    @115
    @28
    @122
    a1i
    ffvelrnda
    #
    @110
    @78
    @101
    @5
    sqsscirc2
    syl21anc
    imp
    @91
    @112
    wa
    #
    @79
    cc
    cxmt
    cfv
    wcel
    #
    @5
    cxr
    wcel
    #
    wa
    #
    @113
    @114
    wa
    #
    @101
    @78
    @79
    co
    #
    @5
    clt
    wbr
    #
    @102
    @125
    @127
    @126
    @91
    @127
    @112
    @91
    @5
    @110
    rpxrd
    adantr
    cnxmet
    jctil
    @125
    @113
    @114
    @91
    @113
    @112
    @123
    adantr
    #
    @91
    @114
    @112
    @124
    adantr
    #
    jca
    @125
    @130
    @111
    @5
    clt
    @125
    @114
    @113
    @130
    @111
    wceq
    @133
    @132
    @101
    @78
    @79
    @79
    eqid
    cnmetdval
    syl2anc
    @91
    @112
    simpr
    eqbrtrd
    @128
    @129
    wa
    @102
    @131
    @101
    @79
    @78
    @5
    cc
    elbl3
    biimpar
    syl21anc
    syldan
    ex
    syld
    @91
    @77
    wfun
    #
    @101
    @77
    cdm
    #
    wcel
    @102
    @104
    wi
    cc
    @46
    @77
    wf1o
    #
    @134
    @117
    @118
    @136
    @120
    @121
    @46
    cc
    cG
    f1ocnv
    mp2b
    #
    cc
    @46
    @77
    f1ofun
    ax-mp
    @91
    @101
    cc
    @135
    @124
    @136
    @135
    cc
    wceq
    @137
    cc
    @46
    @77
    f1odm
    ax-mp
    syl6eleqr
    @81
    @101
    @77
    funfvima
    sylancr
    @91
    @104
    @89
    @91
    @103
    @30
    @82
    @91
    @118
    @90
    @103
    @30
    wceq
    @117
    @118
    @91
    @120
    @121
    mp1i
    @109
    @46
    cc
    @30
    cG
    f1ocnvfv1
    syl2anc
    eleq1d
    biimpd
    3syld
    imp
    syl
    ex
    ssrdv
    ralrimiva
    @3
    @81
    cG
    cA
    cima
    #
    wss
    #
    vd
    crp
    wrex
    #
    @87
    @3
    @78
    @138
    wcel
    #
    vm
    cv
    #
    @5
    @80
    co
    #
    @138
    wss
    #
    vd
    crp
    wrex
    #
    vm
    @138
    wral
    #
    @140
    @3
    cG
    wfun
    #
    cX
    cG
    cdm
    #
    wcel
    #
    @2
    @141
    @147
    @3
    vu
    vv
    cr
    cr
    vu
    cv
    ci
    vv
    cv
    cmul
    co
    caddc
    co
    cG
    tpr2rico.1
    mpt2fun
    a1i
    @3
    cX
    @46
    @148
    @1
    cA
    @46
    cX
    @53
    sselda
    @117
    @118
    @148
    @46
    wceq
    @120
    @121
    @46
    cc
    cG
    f1odm
    mp2b
    syl6eleqr
    @1
    @2
    simpr
    @147
    @149
    wa
    @2
    @141
    cA
    cX
    cG
    funfvima
    imp
    syl21anc
    @1
    @146
    @2
    @1
    @138
    @116
    wcel
    #
    @146
    @117
    @1
    @150
    @120
    cA
    cG
    @0
    @116
    hmeoima
    mpan
    @150
    @138
    cc
    wss
    #
    @146
    @126
    @150
    @151
    @146
    wa
    wb
    cnxmet
    vm
    vd
    @138
    @79
    @116
    cc
    @116
    @119
    cnfldtopn
    elmopn2
    ax-mp
    simprbi
    syl
    adantr
    @145
    @140
    vm
    @78
    @138
    @142
    @78
    wceq
    #
    @144
    @139
    vd
    crp
    @152
    @143
    @81
    @138
    @142
    @78
    @5
    @80
    oveq1
    sseq1d
    rexbidv
    rspcva
    syl2anc
    @1
    @140
    @87
    wi
    @2
    @1
    @139
    @84
    vd
    crp
    @139
    @82
    @77
    @138
    cima
    #
    wss
    @1
    @84
    @81
    @138
    @77
    imass2
    @1
    @153
    cA
    @82
    @1
    @46
    cc
    cG
    wf1
    #
    @48
    @153
    cA
    wceq
    @117
    @118
    @154
    @120
    @121
    @46
    cc
    cG
    f1of1
    mp2b
    @53
    @46
    cc
    cA
    cG
    f1imacnv
    sylancr
    sseq2d
    syl5ib
    reximdv
    adantr
    mpd
    @83
    @84
    vd
    crp
    r19.29
    syl2anc
    @85
    @17
    vd
    crp
    @14
    @82
    cA
    sstr
    reximi
    syl
    @16
    @17
    vd
    crp
    r19.29
    syl2anc
    @15
    @18
    vd
    crp
    r19.29
    syl2anc
    @19
    @25
    vd
    crp
    @24
    @18
    vr
    @14
    cB
    @21
    @14
    wceq
    @22
    @16
    @23
    @17
    @21
    @14
    cX
    eleq2
    @21
    @14
    cA
    sseq1
    anbi12d
    rspcev
    rexlimivw
    syl
end
