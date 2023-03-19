include "cmbf.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "ccnv.mm"
include "cima.mm"
include "cuni.mm"
include "wceq.mm"
include "cvol.mm"
include "cdm.mm"
include "wex.mm"
include "ctg.mm"
include "cfv.mm"
include "cioo.mm"
include "crn.mm"
include "ctx.mm"
include "co.mm"
include "ccn.mm"
include "chmeo.mm"
include "eqid.mm"
include "cnrehmeo.mm"
include "hmeocn.mm"
include "ax-mp.mm"
include "cnima.mm"
include "mpan.mm"
include "cq.mm"
include "cxp.mm"
include "fveq2i.mm"
include "tgqioo.mm"
include "oveq12i.mm"
include "ctb.mm"
include "qtopbas.mm"
include "eqeltri.mm"
include "txbasval.mm"
include "mp2an.mm"
include "txval.mm"
include "3eqtri.mm"
include "syl6eleq.mm"
include "wb.mm"
include "txbas.mm"
include "eltg3.mm"
include "sylib.mm"
include "adantl.mm"
include "ciun.mm"
include "cr.mm"
include "cc.mm"
include "wfo.mm"
include "wf1o.mm"
include "cnref1o.mm"
include "f1ofo.mm"
include "elssuni.mm"
include "cnfldtopon.mm"
include "toponunii.mm"
include "syl6sseqr.mm"
include "ad2antlr.mm"
include "foimacnv.mm"
include "sylancr.mm"
include "simprr.mm"
include "imaeq2d.mm"
include "imauni.mm"
include "syl6eq.mm"
include "eqtr3d.mm"
include "imaiun.mm"
include "cn.mm"
include "cdom.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "ssdomg.mm"
include "cmpt2.mm"
include "ccrd.mm"
include "com.mm"
include "con0.mm"
include "cen.mm"
include "omelon.mm"
include "nnenom.mm"
include "ensymi.mm"
include "isnumi.mm"
include "cres.mm"
include "qnnen.mm"
include "xpen.mm"
include "xpnnen.mm"
include "entri.mm"
include "entr2i.mm"
include "wfun.mm"
include "cxr.mm"
include "cpw.mm"
include "wf.mm"
include "ioof.mm"
include "ffun.mm"
include "qssre.mm"
include "ressxr.mm"
include "sstri.mm"
include "xpss12.mm"
include "fdmi.mm"
include "sseqtr4i.mm"
include "fores.mm"
include "fodomnum.mm"
include "mp2.mm"
include "eqbrtri.mm"
include "domentr.mm"
include "elexi.mm"
include "xpdom1.mm"
include "nnex.mm"
include "xpdom2.mm"
include "domtr.mm"
include "numdom.mm"
include "wfn.mm"
include "vex.mm"
include "xpex.mm"
include "fnmpt2i.mm"
include "dffn4.mm"
include "mpbi.mm"
include "sylancl.mm"
include "ad2antrl.mm"
include "wrex.mm"
include "eleq2i.mm"
include "elrnmpt2.mm"
include "bitri.mm"
include "cre.mm"
include "ccom.mm"
include "cim.mm"
include "cin.mm"
include "elin.mm"
include "mbff.mm"
include "adantr.mm"
include "fvco3.mm"
include "sylan.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "cop.mm"
include "ffvelrnda.mm"
include "fveq2.mm"
include "opeq12d.mm"
include "cnrecnv.mm"
include "opex.mm"
include "fvmpt.mm"
include "syl.mm"
include "biantrurd.mm"
include "bitr3d.mm"
include "opelxp.mm"
include "f1ocnv.mm"
include "f1ofn.mm"
include "mp2b.mm"
include "elpreima.mm"
include "imacnvcnv.mm"
include "bitr3i.mm"
include "3bitr3g.mm"
include "bitrd.mm"
include "pm5.32da.mm"
include "ref.mm"
include "fco.mm"
include "ffn.mm"
include "3syl.mm"
include "imf.mm"
include "anandi.mm"
include "syl6bbr.mm"
include "3bitr4d.mm"
include "syl5bb.mm"
include "eqrdv.mm"
include "ismbfcn.mm"
include "ibi.mm"
include "simpld.mm"
include "ismbf.mm"
include "mpbid.mm"
include "imassrn.mm"
include "eqsstri.mm"
include "simprl.mm"
include "sseldi.mm"
include "rsp.mm"
include "sylc.mm"
include "simprd.mm"
include "inmbl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "imaeq2.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "ssralv.mm"
include "mpan9.mm"
include "ad2ant2r.mm"
include "iunmbl2.mm"
include "eqeltrd.mm"
include "exlimddv.mm"

theorem mbfimaopnlem
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let vt: setvar t
  let vu: setvar u
  let vz: setvar z
  let cC: class C
  let vw: setvar w
  assume mbfimaopn.1: |- J = ( TopOpen ` CCfld )
  assume mbfimaopn.2: |- G = ( x e. RR , y e. RR |-> ( x + ( _i x. y ) ) )
  assume mbfimaopn.3: |- B = ( (,) " ( QQ X. QQ ) )
  assume mbfimaopn.4: |- K = ran ( x e. B , y e. B |-> ( x X. y ) )

  disjoint A x
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint G x
  disjoint G y
  disjoint J x
  disjoint J y
  disjoint t u
  disjoint t x
  disjoint A t
  disjoint u x
  disjoint A u
  disjoint u y
  disjoint u z
  disjoint B u
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint C u
  disjoint t w
  disjoint t y
  disjoint t z
  disjoint F t
  disjoint u w
  disjoint F u
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint K t
  disjoint K w
  disjoint G t
  disjoint G w
  disjoint G z
  disjoint J t
  disjoint J u
  assert |- ( ( F e. MblFn /\ A e. J ) -> ( `' F " A ) e. dom vol )

  proof
    cF
    cmbf
    wcel
    #
    cA
    cJ
    wcel
    #
    wa
    #
    vt
    cv
    #
    cK
    wss
    #
    cG
    ccnv
    #
    cA
    cima
    #
    @3
    cuni
    #
    wceq
    #
    wa
    #
    cF
    ccnv
    #
    cA
    cima
    #
    cvol
    cdm
    #
    wcel
    vt
    @1
    @9
    vt
    wex
    #
    @0
    @1
    @6
    cK
    ctg
    cfv
    #
    wcel
    #
    @13
    @1
    @6
    cioo
    crn
    #
    ctg
    cfv
    #
    @17
    ctx
    co
    #
    @14
    cG
    @18
    cJ
    ccn
    co
    wcel
    #
    @1
    @6
    @18
    wcel
    cG
    @18
    cJ
    chmeo
    co
    wcel
    @19
    vx
    vy
    cG
    @17
    cJ
    mbfimaopn.2
    @17
    eqid
    mbfimaopn.1
    cnrehmeo
    cG
    @18
    cJ
    hmeocn
    ax-mp
    cA
    cG
    @18
    cJ
    cnima
    mpan
    @18
    cB
    ctg
    cfv
    #
    @20
    ctx
    co
    #
    cB
    cB
    ctx
    co
    #
    @14
    @17
    @20
    @17
    @20
    ctx
    @20
    cB
    cioo
    cq
    cq
    cxp
    #
    cima
    #
    ctg
    mbfimaopn.3
    fveq2i
    tgqioo
    #
    @25
    oveq12i
    cB
    ctb
    wcel
    #
    @26
    @21
    @22
    wceq
    cB
    @24
    ctb
    mbfimaopn.3
    qtopbas
    eqeltri
    #
    @27
    cB
    cB
    ctb
    ctb
    txbasval
    mp2an
    @26
    @26
    @22
    @14
    wceq
    @27
    @27
    vx
    vy
    cK
    cB
    cB
    ctb
    ctb
    mbfimaopn.4
    txval
    mp2an
    3eqtri
    syl6eleq
    cK
    ctb
    wcel
    #
    @15
    @13
    wb
    @26
    @26
    @28
    @27
    @27
    vx
    vy
    cK
    cB
    cB
    mbfimaopn.4
    txbas
    mp2an
    #
    vt
    @6
    cK
    ctb
    eltg3
    ax-mp
    sylib
    adantl
    @2
    @9
    wa
    #
    @11
    vw
    @3
    @10
    cG
    vw
    cv
    #
    cima
    #
    cima
    #
    ciun
    #
    @12
    @30
    @11
    @10
    vw
    @3
    @32
    ciun
    #
    cima
    @34
    @30
    cA
    @35
    @10
    @30
    cG
    @6
    cima
    #
    cA
    @35
    @30
    cr
    cr
    cxp
    #
    cc
    cG
    wfo
    #
    cA
    cc
    wss
    #
    @36
    cA
    wceq
    @37
    cc
    cG
    wf1o
    #
    @38
    vx
    vy
    cG
    mbfimaopn.2
    cnref1o
    #
    @37
    cc
    cG
    f1ofo
    ax-mp
    @1
    @39
    @0
    @9
    @1
    cA
    cJ
    cuni
    cc
    cA
    cJ
    elssuni
    cc
    cJ
    cJ
    mbfimaopn.1
    cnfldtopon
    toponunii
    syl6sseqr
    ad2antlr
    @37
    cc
    cA
    cG
    foimacnv
    sylancr
    @30
    @36
    cG
    @7
    cima
    @35
    @30
    @6
    @7
    cG
    @2
    @4
    @8
    simprr
    imaeq2d
    vw
    cG
    @3
    imauni
    syl6eq
    eqtr3d
    imaeq2d
    vw
    @10
    @3
    @32
    imaiun
    syl6eq
    @30
    @3
    cn
    cdom
    wbr
    #
    @33
    @12
    wcel
    #
    vw
    @3
    wral
    #
    @34
    @12
    wcel
    @4
    @42
    @2
    @8
    @4
    @3
    cK
    cdom
    wbr
    #
    cK
    cn
    cdom
    wbr
    @42
    @28
    @4
    @45
    wi
    @29
    @3
    cK
    ctb
    ssdomg
    ax-mp
    cK
    vx
    vy
    cB
    cB
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
    cn
    cdom
    mbfimaopn.4
    @50
    cB
    cB
    cxp
    #
    cdom
    wbr
    #
    @51
    cn
    cdom
    wbr
    #
    @50
    cn
    cdom
    wbr
    @51
    ccrd
    cdm
    #
    wcel
    #
    @51
    @50
    @49
    wfo
    #
    @52
    cn
    @54
    wcel
    #
    @53
    @55
    com
    con0
    wcel
    #
    com
    cn
    cen
    wbr
    @57
    omelon
    cn
    com
    nnenom
    ensymi
    com
    cn
    isnumi
    mp2an
    @51
    cn
    cn
    cxp
    #
    cdom
    wbr
    #
    @59
    cn
    cen
    wbr
    @53
    @51
    cn
    cB
    cxp
    #
    cdom
    wbr
    #
    @61
    @59
    cdom
    wbr
    #
    @60
    cB
    cn
    cdom
    wbr
    #
    @62
    cB
    @23
    cdom
    wbr
    @23
    cn
    cen
    wbr
    @64
    cB
    @24
    @23
    cdom
    mbfimaopn.3
    @23
    @54
    wcel
    #
    @23
    @24
    cioo
    @23
    cres
    #
    wfo
    #
    @24
    @23
    cdom
    wbr
    @58
    com
    @23
    cen
    wbr
    @65
    omelon
    @23
    cn
    com
    @23
    @59
    cn
    cq
    cn
    cen
    wbr
    #
    @68
    @23
    @59
    cen
    wbr
    qnnen
    qnnen
    cq
    cn
    cq
    cn
    xpen
    mp2an
    xpnnen
    entri
    #
    nnenom
    entr2i
    com
    @23
    isnumi
    mp2an
    cioo
    wfun
    #
    @23
    cioo
    cdm
    #
    wss
    @67
    cxr
    cxr
    cxp
    #
    cr
    cpw
    #
    cioo
    wf
    @70
    ioof
    @72
    @73
    cioo
    ffun
    ax-mp
    @23
    @72
    @71
    cq
    cxr
    wss
    #
    @74
    @23
    @72
    wss
    cq
    cr
    cxr
    qssre
    ressxr
    sstri
    #
    @75
    cq
    cxr
    cq
    cxr
    xpss12
    mp2an
    @72
    @73
    cioo
    ioof
    fdmi
    sseqtr4i
    @23
    cioo
    fores
    mp2an
    @23
    @24
    @66
    fodomnum
    mp2
    eqbrtri
    @69
    cB
    @23
    cn
    domentr
    mp2an
    #
    cB
    cn
    cB
    cB
    ctb
    @27
    elexi
    xpdom1
    ax-mp
    @64
    @63
    @76
    cB
    cn
    cn
    nnex
    xpdom2
    ax-mp
    @51
    @61
    @59
    domtr
    mp2an
    xpnnen
    @51
    @59
    cn
    domentr
    mp2an
    #
    cn
    @51
    numdom
    mp2an
    @49
    @51
    wfn
    @56
    vx
    vy
    cB
    cB
    @48
    @49
    @49
    eqid
    #
    @46
    @47
    vx
    vex
    vy
    vex
    xpex
    #
    fnmpt2i
    @51
    @49
    dffn4
    mpbi
    @51
    @50
    @49
    fodomnum
    mp2
    @77
    @50
    @51
    cn
    domtr
    mp2an
    eqbrtri
    @3
    cK
    cn
    domtr
    sylancl
    ad2antrl
    @0
    @4
    @44
    @1
    @8
    @0
    @43
    vw
    cK
    wral
    @4
    @44
    @0
    @43
    vw
    cK
    @31
    cK
    wcel
    #
    @31
    @48
    wceq
    #
    vy
    cB
    wrex
    vx
    cB
    wrex
    #
    @0
    @43
    @80
    @31
    @50
    wcel
    @82
    cK
    @50
    @31
    mbfimaopn.4
    eleq2i
    vx
    vy
    cB
    cB
    @48
    @31
    @49
    @78
    @79
    elrnmpt2
    bitri
    @0
    @81
    @43
    vx
    vy
    cB
    cB
    @0
    @46
    cB
    wcel
    #
    @47
    cB
    wcel
    #
    wa
    #
    wa
    #
    @43
    @81
    @10
    cG
    @48
    cima
    #
    cima
    #
    @12
    wcel
    @86
    cre
    cF
    ccom
    #
    ccnv
    @46
    cima
    #
    cim
    cF
    ccom
    #
    ccnv
    @47
    cima
    #
    cin
    #
    @88
    @12
    @86
    vz
    @93
    @88
    vz
    cv
    #
    @93
    wcel
    @94
    @90
    wcel
    #
    @94
    @92
    wcel
    #
    wa
    #
    @86
    @94
    @88
    wcel
    #
    @94
    @90
    @92
    elin
    @86
    @94
    cF
    cdm
    #
    wcel
    #
    @94
    @89
    cfv
    #
    @46
    wcel
    #
    @94
    @91
    cfv
    #
    @47
    wcel
    #
    wa
    #
    wa
    #
    @100
    @94
    cF
    cfv
    #
    @87
    wcel
    #
    wa
    #
    @97
    @98
    @86
    @100
    @105
    @108
    @86
    @100
    wa
    #
    @105
    @107
    cre
    cfv
    #
    @46
    wcel
    #
    @107
    cim
    cfv
    #
    @47
    wcel
    #
    wa
    #
    @108
    @110
    @102
    @112
    @104
    @114
    @110
    @101
    @111
    @46
    @86
    @99
    cc
    cF
    wf
    #
    @100
    @101
    @111
    wceq
    @0
    @116
    @85
    cF
    mbff
    #
    adantr
    #
    @99
    cc
    @94
    cre
    cF
    fvco3
    sylan
    eleq1d
    @110
    @103
    @113
    @47
    @86
    @116
    @100
    @103
    @113
    wceq
    @118
    @99
    cc
    @94
    cim
    cF
    fvco3
    sylan
    eleq1d
    anbi12d
    @110
    @111
    @113
    cop
    #
    @48
    wcel
    #
    @107
    cc
    wcel
    #
    @107
    @5
    cfv
    #
    @48
    wcel
    #
    wa
    #
    @115
    @108
    @110
    @123
    @120
    @124
    @110
    @122
    @119
    @48
    @110
    @121
    @122
    @119
    wceq
    @86
    @99
    cc
    @94
    cF
    @118
    ffvelrnda
    #
    vw
    @107
    @31
    cre
    cfv
    #
    @31
    cim
    cfv
    #
    cop
    @119
    cc
    @5
    @31
    @107
    wceq
    @126
    @111
    @127
    @113
    @31
    @107
    cre
    fveq2
    @31
    @107
    cim
    fveq2
    opeq12d
    vx
    vy
    vw
    cG
    mbfimaopn.2
    cnrecnv
    @111
    @113
    opex
    fvmpt
    syl
    eleq1d
    @110
    @121
    @123
    @125
    biantrurd
    bitr3d
    @111
    @113
    @46
    @47
    opelxp
    @124
    @107
    @5
    ccnv
    @48
    cima
    #
    wcel
    #
    @108
    @5
    cc
    wfn
    #
    @129
    @124
    wb
    @40
    cc
    @37
    @5
    wf1o
    @130
    @41
    @37
    cc
    cG
    f1ocnv
    cc
    @37
    @5
    f1ofn
    mp2b
    cc
    @107
    @48
    @5
    elpreima
    ax-mp
    @128
    @87
    @107
    cG
    @48
    imacnvcnv
    eleq2i
    bitr3i
    3bitr3g
    bitrd
    pm5.32da
    @0
    @97
    @106
    wb
    @85
    @0
    @97
    @100
    @102
    wa
    #
    @100
    @104
    wa
    #
    wa
    @106
    @0
    @95
    @131
    @96
    @132
    @0
    @99
    cr
    @89
    wf
    #
    @89
    @99
    wfn
    @95
    @131
    wb
    @0
    cc
    cr
    cre
    wf
    @116
    @133
    ref
    @117
    @99
    cc
    cr
    cre
    cF
    fco
    sylancr
    #
    @99
    cr
    @89
    ffn
    @99
    @94
    @46
    @89
    elpreima
    3syl
    @0
    @99
    cr
    @91
    wf
    #
    @91
    @99
    wfn
    @96
    @132
    wb
    @0
    cc
    cr
    cim
    wf
    @116
    @135
    imf
    @117
    @99
    cc
    cr
    cim
    cF
    fco
    sylancr
    #
    @99
    cr
    @91
    ffn
    @99
    @94
    @47
    @91
    elpreima
    3syl
    anbi12d
    @100
    @102
    @104
    anandi
    syl6bbr
    adantr
    @0
    @98
    @109
    wb
    #
    @85
    @0
    @116
    cF
    @99
    wfn
    @137
    @117
    @99
    cc
    cF
    ffn
    @99
    @94
    @87
    cF
    elpreima
    3syl
    adantr
    3bitr4d
    syl5bb
    eqrdv
    @86
    @90
    @12
    wcel
    #
    @92
    @12
    wcel
    #
    @93
    @12
    wcel
    @86
    @138
    vx
    @16
    wral
    #
    @46
    @16
    wcel
    @138
    @0
    @140
    @85
    @0
    @89
    cmbf
    wcel
    #
    @140
    @0
    @141
    @91
    cmbf
    wcel
    #
    @0
    @141
    @142
    wa
    #
    @0
    @116
    @0
    @143
    wb
    @117
    @99
    cF
    ismbfcn
    syl
    ibi
    #
    simpld
    @0
    @133
    @141
    @140
    wb
    @134
    vx
    @99
    @89
    ismbf
    syl
    mpbid
    adantr
    @86
    cB
    @16
    @46
    cB
    @24
    @16
    mbfimaopn.3
    cioo
    @23
    imassrn
    eqsstri
    #
    @0
    @83
    @84
    simprl
    sseldi
    @138
    vx
    @16
    rsp
    sylc
    @86
    @139
    vy
    @16
    wral
    #
    @47
    @16
    wcel
    @139
    @0
    @146
    @85
    @0
    @142
    @146
    @0
    @141
    @142
    @144
    simprd
    @0
    @135
    @142
    @146
    wb
    @136
    vy
    @99
    @91
    ismbf
    syl
    mpbid
    adantr
    @86
    cB
    @16
    @47
    @145
    @0
    @83
    @84
    simprr
    sseldi
    @139
    vy
    @16
    rsp
    sylc
    @90
    @92
    inmbl
    syl2anc
    eqeltrrd
    @81
    @33
    @88
    @12
    @81
    @32
    @87
    @10
    @31
    @48
    cG
    imaeq2
    imaeq2d
    eleq1d
    syl5ibrcom
    rexlimdvva
    syl5bi
    ralrimiv
    @43
    vw
    @3
    cK
    ssralv
    mpan9
    ad2ant2r
    @3
    @33
    vw
    iunmbl2
    syl2anc
    eqeltrd
    exlimddv
end
