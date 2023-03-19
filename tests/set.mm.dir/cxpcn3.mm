include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cv.mm"
include "ccxp.mm"
include "cmpt2.mm"
include "ctx.mm"
include "ccn.mm"
include "wcel.mm"
include "cxp.mm"
include "cc.mm"
include "wf.mm"
include "ccnp.mm"
include "cfv.mm"
include "wral.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "sseli.mm"
include "cre.mm"
include "ccnv.mm"
include "crp.mm"
include "cima.mm"
include "cdm.mm"
include "cnvimass.mm"
include "ref.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "eqsstri.mm"
include "cxpcl.mm"
include "syl2an.mm"
include "rgen2.mm"
include "eqid.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "cop.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wceq.mm"
include "cres.mm"
include "crest.mm"
include "ctopon.mm"
include "wss.mm"
include "cnfldtopon.mm"
include "cle.mm"
include "rpre.mm"
include "rpge0.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "ssriv.mm"
include "resttopon.mm"
include "mp2an.mm"
include "toponunii.mm"
include "restid.mm"
include "ax-mp.mm"
include "eqcomi.mm"
include "a1i.mm"
include "ssid.mm"
include "cxpcn2.mm"
include "cnmpt2res.mm"
include "simplbi.mm"
include "adantr.mm"
include "simpr.mm"
include "elrpd.mm"
include "simplr.mm"
include "opelxp.mm"
include "eqeltri.mm"
include "txtopon.mm"
include "cncnpi.mm"
include "syl2anc.mm"
include "resmpt2.mm"
include "cioo.mm"
include "crn.mm"
include "ctg.mm"
include "ioorp.mm"
include "iooretop.mm"
include "eqeltrri.mm"
include "wb.mm"
include "ctop.mm"
include "cvv.mm"
include "w3a.mm"
include "retop.mm"
include "ovex.mm"
include "restopnb.mm"
include "mpanl12.mm"
include "mp3an.mm"
include "rerest.mm"
include "eqtri.mm"
include "eleqtrri.mm"
include "toponmax.mm"
include "txrest.mm"
include "mp4an.mm"
include "oveq1i.mm"
include "restabs.mm"
include "oveq12i.mm"
include "fveq1i.mm"
include "3eltr4g.mm"
include "cnt.mm"
include "topontopi.mm"
include "xpss1.mm"
include "mp1i.mm"
include "txopn.mm"
include "isopn3i.mm"
include "syl6eleqr.mm"
include "txunii.mm"
include "cnprest.mm"
include "syl22anc.mm"
include "mpbird.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "wi.mm"
include "wrex.mm"
include "c1.mm"
include "cif.mm"
include "c2.mm"
include "cdiv.mm"
include "cxpcn3lem.mm"
include "ralrimiva.mm"
include "0e0icopnf.mm"
include "simprl.mm"
include "ovresd.mm"
include "0cn.mm"
include "sseldi.mm"
include "cnmetdval.mm"
include "sylancr.mm"
include "cneg.mm"
include "df-neg.mm"
include "fveq2i.mm"
include "absnegd.mm"
include "syl5eqr.mm"
include "3eqtrd.mm"
include "breq1d.mm"
include "simpl.mm"
include "simprr.mm"
include "eqtrd.mm"
include "anbi12d.mm"
include "oveq12.mm"
include "ovmpt2a.mm"
include "eleq2i.mm"
include "wfn.mm"
include "ffn.mm"
include "elpreima.mm"
include "mp2b.mm"
include "bitri.mm"
include "wne.mm"
include "simprbi.mm"
include "rpne0d.mm"
include "fveq2.mm"
include "re0.mm"
include "syl6eq.mm"
include "necon3i.mm"
include "syl.mm"
include "0cxpd.mm"
include "adantl.mm"
include "oveq12d.mm"
include "cxpcld.mm"
include "imbi12d.mm"
include "2ralbidva.mm"
include "rexbidv.mm"
include "ralbidv.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "xmetres2.mm"
include "sylancl.mm"
include "id.mm"
include "cmopn.mm"
include "cnfldtopn.mm"
include "metrest.mm"
include "txmetcnp.mm"
include "syl32anc.mm"
include "mpbir2and.mm"
include "ad2antlr.mm"
include "opeq1d.mm"
include "fveq2d.mm"
include "eleqtrd.mm"
include "wo.mm"
include "0re.mm"
include "leloe.mm"
include "mpbid.mm"
include "mpjaodan.mm"
include "eleq2d.mm"
include "ralxp.mm"
include "mpbir.mm"
include "cncnp.mm"
include "mpbir2an.mm"

theorem cxpcn3
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let cJ: class J
  let cK: class K
  let cL: class L
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cA: class A
  let cE: class E
  let ve: setvar e
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cT: class T
  assume cxpcn3.d: |- D = ( `' Re " RR+ )
  assume cxpcn3.j: |- J = ( TopOpen ` CCfld )
  assume cxpcn3.k: |- K = ( J |`t ( 0 [,) +oo ) )
  assume cxpcn3.l: |- L = ( J |`t D )

  disjoint x y
  disjoint J x
  disjoint J y
  disjoint D x
  disjoint D y
  disjoint a b
  disjoint a d
  disjoint A a
  disjoint b d
  disjoint A b
  disjoint A d
  disjoint E a
  disjoint E b
  disjoint E d
  disjoint d e
  disjoint d u
  disjoint d v
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint J d
  disjoint e u
  disjoint e v
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint J e
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint J u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint J v
  disjoint x z
  disjoint y z
  disjoint J z
  disjoint a e
  disjoint a u
  disjoint a v
  disjoint a z
  disjoint K a
  disjoint b e
  disjoint b u
  disjoint b v
  disjoint b z
  disjoint K b
  disjoint K d
  disjoint K e
  disjoint K u
  disjoint K v
  disjoint K z
  disjoint a x
  disjoint a y
  disjoint D a
  disjoint b x
  disjoint b y
  disjoint D b
  disjoint D d
  disjoint D e
  disjoint D u
  disjoint D v
  disjoint D z
  disjoint L a
  disjoint L b
  disjoint L d
  disjoint L e
  disjoint L u
  disjoint L v
  disjoint L z
  disjoint T a
  disjoint T b
  disjoint T d
  assert |- ( x e. ( 0 [,) +oo ) , y e. D |-> ( x ^c y ) ) e. ( ( K tX L ) Cn J )

  proof
    vx
    vy
    cc0
    cpnf
    cico
    co
    #
    cD
    vx
    cv
    #
    vy
    cv
    #
    ccxp
    co
    #
    cmpt2
    #
    cK
    cL
    ctx
    co
    #
    cJ
    ccn
    co
    wcel
    #
    @0
    cD
    cxp
    #
    cc
    @4
    wf
    #
    @4
    vz
    cv
    #
    @5
    cJ
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    vz
    @7
    wral
    #
    @3
    cc
    wcel
    #
    vy
    cD
    wral
    vx
    @0
    wral
    @8
    @14
    vx
    vy
    @0
    cD
    @1
    @0
    wcel
    #
    @1
    cc
    wcel
    @2
    cc
    wcel
    @14
    @2
    cD
    wcel
    @0
    cc
    @1
    @0
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    #
    sseli
    cD
    cc
    @2
    cD
    cre
    ccnv
    crp
    cima
    #
    cc
    cxpcn3.d
    @17
    cre
    cdm
    cc
    cre
    crp
    cnvimass
    cc
    cr
    cre
    ref
    fdmi
    sseqtri
    eqsstri
    #
    sseli
    @1
    @2
    cxpcl
    syl2an
    rgen2
    vx
    vy
    @0
    cD
    @3
    cc
    @4
    @4
    eqid
    #
    fmpt2
    mpbi
    #
    @13
    @4
    vu
    cv
    #
    vv
    cv
    #
    cop
    #
    @10
    cfv
    #
    wcel
    #
    vv
    cD
    wral
    vu
    @0
    wral
    @25
    vu
    vv
    @0
    cD
    @21
    @0
    wcel
    #
    @22
    cD
    wcel
    #
    wa
    #
    cc0
    @21
    clt
    wbr
    #
    @25
    cc0
    @21
    wceq
    #
    @28
    @29
    wa
    #
    @25
    @4
    crp
    cD
    cxp
    #
    cres
    #
    @23
    @5
    @32
    crest
    co
    #
    cJ
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @31
    vx
    vy
    crp
    cD
    @3
    cmpt2
    #
    @23
    cJ
    crp
    crest
    co
    #
    cL
    ctx
    co
    #
    cJ
    ccnp
    co
    #
    cfv
    #
    @33
    @36
    @31
    @38
    @40
    cJ
    ccn
    co
    wcel
    @23
    @32
    wcel
    #
    @38
    @42
    wcel
    @31
    vx
    vy
    @3
    @39
    @39
    cJ
    cJ
    cL
    cD
    crp
    crp
    cc
    @39
    crp
    crest
    co
    #
    @39
    @39
    crp
    ctopon
    cfv
    #
    wcel
    #
    @44
    @39
    wceq
    cJ
    cc
    ctopon
    cfv
    #
    wcel
    #
    crp
    cc
    wss
    @46
    cJ
    cxpcn3.j
    cnfldtopon
    #
    crp
    @0
    cc
    vx
    crp
    @0
    @1
    crp
    wcel
    @1
    cr
    wcel
    cc0
    @1
    cle
    wbr
    @15
    @1
    rpre
    @1
    rpge0
    @1
    elrege0
    sylanbrc
    ssriv
    #
    @16
    sstri
    crp
    cJ
    cc
    resttopon
    mp2an
    #
    @39
    @45
    crp
    crp
    @39
    @51
    toponunii
    restid
    ax-mp
    eqcomi
    @46
    @31
    @51
    a1i
    crp
    crp
    wss
    #
    @31
    crp
    ssid
    #
    a1i
    cxpcn3.l
    @48
    @31
    @49
    a1i
    cD
    cc
    wss
    #
    @31
    @18
    a1i
    vx
    vy
    crp
    cc
    @3
    cmpt2
    @39
    cJ
    ctx
    co
    cJ
    ccn
    co
    wcel
    @31
    vx
    vy
    cJ
    @39
    cxpcn3.j
    @39
    eqid
    cxpcn2
    a1i
    cnmpt2res
    @31
    @21
    crp
    wcel
    @27
    @43
    @31
    @21
    @28
    @21
    cr
    wcel
    #
    @29
    @26
    @55
    @27
    @26
    @55
    cc0
    @21
    cle
    wbr
    #
    @21
    elrege0
    #
    simplbi
    adantr
    #
    adantr
    @28
    @29
    simpr
    elrpd
    @26
    @27
    @29
    simplr
    @21
    @22
    crp
    cD
    opelxp
    sylanbrc
    #
    @23
    @38
    @40
    cJ
    @32
    @32
    @40
    @46
    cL
    cD
    ctopon
    cfv
    #
    wcel
    #
    @40
    @32
    ctopon
    cfv
    wcel
    @51
    cL
    cJ
    cD
    crest
    co
    #
    @60
    cxpcn3.l
    @48
    @54
    @62
    @60
    wcel
    @49
    @18
    cD
    cJ
    cc
    resttopon
    mp2an
    eqeltri
    #
    @39
    cL
    crp
    cD
    txtopon
    mp2an
    toponunii
    cncnpi
    syl2anc
    crp
    @0
    wss
    #
    cD
    cD
    wss
    @33
    @38
    wceq
    @50
    cD
    ssid
    vx
    vy
    @0
    cD
    crp
    cD
    @3
    resmpt2
    mp2an
    @23
    @35
    @41
    @34
    @40
    cJ
    ccnp
    @34
    cK
    crp
    crest
    co
    #
    cL
    cD
    crest
    co
    #
    ctx
    co
    #
    @40
    cK
    @0
    ctopon
    cfv
    #
    wcel
    #
    @61
    crp
    cK
    wcel
    #
    cD
    cL
    wcel
    #
    @34
    @67
    wceq
    cK
    cJ
    @0
    crest
    co
    #
    @68
    cxpcn3.k
    @48
    @0
    cc
    wss
    #
    @72
    @68
    wcel
    @49
    @16
    @0
    cJ
    cc
    resttopon
    mp2an
    eqeltri
    #
    @63
    crp
    cioo
    crn
    ctg
    cfv
    #
    @0
    crest
    co
    #
    cK
    crp
    @75
    wcel
    #
    crp
    @76
    wcel
    #
    cc0
    cpnf
    cioo
    co
    crp
    @75
    ioorp
    cc0
    cpnf
    iooretop
    eqeltrri
    #
    @77
    @64
    @52
    @77
    @78
    wb
    #
    @79
    @50
    @53
    @75
    ctop
    wcel
    @0
    cvv
    wcel
    #
    @77
    @64
    @52
    w3a
    @80
    retop
    cc0
    cpnf
    cico
    ovex
    #
    @0
    crp
    crp
    @75
    cvv
    restopnb
    mpanl12
    mp3an
    mpbi
    cK
    @72
    @76
    cxpcn3.k
    @0
    cr
    wss
    @72
    @76
    wceq
    rge0ssre
    @0
    @75
    cJ
    cxpcn3.j
    @75
    eqid
    rerest
    ax-mp
    eqtri
    eleqtrri
    #
    @61
    @71
    @63
    cD
    cL
    toponmax
    ax-mp
    #
    crp
    cD
    cK
    cL
    @68
    @60
    cK
    cL
    txrest
    mp4an
    @65
    @39
    @66
    cL
    ctx
    @65
    @72
    crp
    crest
    co
    #
    @39
    cK
    @72
    crp
    crest
    cxpcn3.k
    oveq1i
    @48
    @64
    @81
    @85
    @39
    wceq
    @49
    @50
    @82
    crp
    @0
    cJ
    @47
    cvv
    restabs
    mp3an
    eqtri
    @61
    @66
    cL
    wceq
    @63
    cL
    @60
    cD
    cD
    cL
    @63
    toponunii
    #
    restid
    ax-mp
    oveq12i
    eqtri
    oveq1i
    fveq1i
    3eltr4g
    @31
    @5
    ctop
    wcel
    #
    @32
    @7
    wss
    #
    @23
    @32
    @5
    cnt
    cfv
    cfv
    #
    wcel
    @8
    @25
    @37
    wb
    @87
    @31
    @7
    @5
    @69
    @61
    @5
    @7
    ctopon
    cfv
    wcel
    #
    @74
    @63
    cK
    cL
    @0
    cD
    txtopon
    mp2an
    #
    topontopi
    #
    a1i
    @64
    @88
    @31
    @50
    crp
    @0
    cD
    xpss1
    mp1i
    @31
    @23
    @32
    @89
    @59
    @87
    @32
    @5
    wcel
    #
    @89
    @32
    wceq
    @92
    @69
    @61
    @70
    @71
    @93
    @74
    @63
    @83
    @84
    crp
    cD
    cK
    cL
    @68
    @60
    txopn
    mp4an
    @32
    @5
    isopn3i
    mp2an
    syl6eleqr
    @8
    @31
    @20
    a1i
    @32
    @23
    @4
    @5
    cJ
    @7
    cc
    cK
    cL
    @0
    cD
    @0
    cK
    @74
    topontopi
    cD
    cL
    @63
    topontopi
    @0
    cK
    @74
    toponunii
    @86
    txunii
    cc
    cJ
    @49
    toponunii
    cnprest
    syl22anc
    mpbird
    @28
    @30
    wa
    #
    @4
    cc0
    @22
    cop
    #
    @10
    cfv
    #
    @24
    @27
    @4
    @96
    wcel
    #
    @26
    @30
    @27
    @97
    @8
    cc0
    va
    cv
    #
    cabs
    cmin
    ccom
    #
    @0
    @0
    cxp
    cres
    #
    co
    #
    vd
    cv
    #
    clt
    wbr
    #
    @22
    vb
    cv
    #
    @99
    cD
    cD
    cxp
    cres
    #
    co
    #
    @102
    clt
    wbr
    #
    wa
    #
    cc0
    @22
    @4
    co
    #
    @98
    @104
    @4
    co
    #
    @99
    co
    #
    ve
    cv
    #
    clt
    wbr
    #
    wi
    #
    vb
    cD
    wral
    va
    @0
    wral
    #
    vd
    crp
    wrex
    #
    ve
    crp
    wral
    #
    @8
    @27
    @20
    a1i
    @27
    @117
    @98
    cabs
    cfv
    #
    @102
    clt
    wbr
    #
    @22
    @104
    cmin
    co
    cabs
    cfv
    #
    @102
    clt
    wbr
    #
    wa
    #
    @98
    @104
    ccxp
    co
    #
    cabs
    cfv
    #
    @112
    clt
    wbr
    #
    wi
    #
    vb
    cD
    wral
    va
    @0
    wral
    #
    vd
    crp
    wrex
    #
    ve
    crp
    wral
    @27
    @128
    ve
    crp
    @22
    cD
    @22
    cre
    cfv
    #
    c1
    cle
    wbr
    @129
    c1
    cif
    c2
    cdiv
    co
    #
    @112
    c1
    @130
    cdiv
    co
    ccxp
    co
    #
    cle
    wbr
    @130
    @131
    cif
    #
    @130
    @112
    cJ
    cK
    cL
    va
    vb
    vd
    cxpcn3.d
    cxpcn3.j
    cxpcn3.k
    cxpcn3.l
    @130
    eqid
    @132
    eqid
    cxpcn3lem
    ralrimiva
    @27
    @116
    @128
    ve
    crp
    @27
    @115
    @127
    vd
    crp
    @27
    @114
    @126
    va
    vb
    @0
    cD
    @27
    @98
    @0
    wcel
    #
    @104
    cD
    wcel
    #
    wa
    #
    wa
    #
    @108
    @122
    @113
    @125
    @136
    @103
    @119
    @107
    @121
    @136
    @101
    @118
    @102
    clt
    @136
    @101
    cc0
    @98
    @99
    co
    #
    cc0
    @98
    cmin
    co
    #
    cabs
    cfv
    #
    @118
    @136
    cc0
    @98
    @99
    @0
    cc0
    @0
    wcel
    #
    @136
    0e0icopnf
    a1i
    @27
    @133
    @134
    simprl
    #
    ovresd
    @136
    cc0
    cc
    wcel
    #
    @98
    cc
    wcel
    @137
    @139
    wceq
    0cn
    @136
    @0
    cc
    @98
    @16
    @141
    sseldi
    #
    cc0
    @98
    @99
    @99
    eqid
    #
    cnmetdval
    sylancr
    @136
    @139
    @98
    cneg
    #
    cabs
    cfv
    @118
    @145
    @138
    cabs
    @98
    df-neg
    fveq2i
    @136
    @98
    @143
    absnegd
    syl5eqr
    3eqtrd
    breq1d
    @136
    @106
    @120
    @102
    clt
    @136
    @106
    @22
    @104
    @99
    co
    #
    @120
    @136
    @22
    @104
    @99
    cD
    @27
    @135
    simpl
    #
    @27
    @133
    @134
    simprr
    #
    ovresd
    @136
    @22
    cc
    wcel
    #
    @104
    cc
    wcel
    @146
    @120
    wceq
    @136
    cD
    cc
    @22
    @18
    @147
    sseldi
    @136
    cD
    cc
    @104
    @18
    @148
    sseldi
    #
    @22
    @104
    @99
    @144
    cnmetdval
    syl2anc
    eqtrd
    breq1d
    anbi12d
    @136
    @111
    @124
    @112
    clt
    @136
    @111
    cc0
    @123
    @99
    co
    #
    cc0
    @123
    cmin
    co
    #
    cabs
    cfv
    #
    @124
    @136
    @109
    cc0
    @110
    @123
    @99
    @136
    @109
    cc0
    @22
    ccxp
    co
    #
    cc0
    @136
    @140
    @27
    @109
    @154
    wceq
    0e0icopnf
    @147
    vx
    vy
    cc0
    @22
    @0
    cD
    @3
    @154
    @4
    @1
    cc0
    @2
    @22
    ccxp
    oveq12
    @19
    cc0
    @22
    ccxp
    ovex
    ovmpt2a
    sylancr
    @27
    @154
    cc0
    wceq
    @135
    @27
    @22
    @27
    @149
    @129
    crp
    wcel
    #
    @27
    @22
    @17
    wcel
    #
    @149
    @155
    wa
    #
    cD
    @17
    @22
    cxpcn3.d
    eleq2i
    cc
    cr
    cre
    wf
    cre
    cc
    wfn
    @156
    @157
    wb
    ref
    cc
    cr
    cre
    ffn
    cc
    @22
    crp
    cre
    elpreima
    mp2b
    bitri
    #
    simplbi
    @27
    @129
    cc0
    wne
    @22
    cc0
    wne
    @27
    @129
    @27
    @149
    @155
    @158
    simprbi
    rpne0d
    @22
    cc0
    @129
    cc0
    @22
    cc0
    wceq
    @129
    cc0
    cre
    cfv
    cc0
    @22
    cc0
    cre
    fveq2
    re0
    syl6eq
    necon3i
    syl
    0cxpd
    adantr
    eqtrd
    @135
    @110
    @123
    wceq
    @27
    vx
    vy
    @98
    @104
    @0
    cD
    @3
    @123
    @4
    @1
    @98
    @2
    @104
    ccxp
    oveq12
    @19
    @98
    @104
    ccxp
    ovex
    ovmpt2a
    adantl
    oveq12d
    @136
    @142
    @123
    cc
    wcel
    @151
    @153
    wceq
    0cn
    @136
    @98
    @104
    @143
    @150
    cxpcld
    #
    cc0
    @123
    @99
    @144
    cnmetdval
    sylancr
    @136
    @153
    @123
    cneg
    #
    cabs
    cfv
    @124
    @160
    @152
    cabs
    @123
    df-neg
    fveq2i
    @136
    @123
    @159
    absnegd
    syl5eqr
    3eqtrd
    breq1d
    imbi12d
    2ralbidva
    rexbidv
    ralbidv
    mpbird
    @27
    @100
    @0
    cxmt
    cfv
    wcel
    #
    @105
    cD
    cxmt
    cfv
    wcel
    #
    @99
    cc
    cxmt
    cfv
    wcel
    #
    @140
    @27
    @97
    @8
    @117
    wa
    wb
    @27
    @163
    @73
    @161
    @163
    @27
    cnxmet
    a1i
    #
    @16
    @99
    @0
    cc
    xmetres2
    sylancl
    @27
    @163
    @54
    @162
    @164
    @18
    @99
    cD
    cc
    xmetres2
    sylancl
    @164
    @140
    @27
    0e0icopnf
    a1i
    @27
    id
    ve
    vd
    vb
    va
    cc0
    @22
    @100
    @105
    @99
    @4
    cK
    cL
    cJ
    @0
    cD
    cc
    cK
    @72
    @100
    cmopn
    cfv
    #
    cxpcn3.k
    @163
    @73
    @72
    @165
    wceq
    cnxmet
    @16
    @99
    @100
    cJ
    @165
    cc
    @0
    @100
    eqid
    cJ
    cxpcn3.j
    cnfldtopn
    #
    @165
    eqid
    metrest
    mp2an
    eqtri
    cL
    @62
    @105
    cmopn
    cfv
    #
    cxpcn3.l
    @163
    @54
    @62
    @167
    wceq
    cnxmet
    @18
    @99
    @105
    cJ
    @167
    cc
    cD
    @105
    eqid
    @166
    @167
    eqid
    metrest
    mp2an
    eqtri
    @166
    txmetcnp
    syl32anc
    mpbir2and
    ad2antlr
    @94
    @95
    @23
    @10
    @94
    cc0
    @21
    @22
    @28
    @30
    simpr
    opeq1d
    fveq2d
    eleqtrd
    @28
    @56
    @29
    @30
    wo
    #
    @26
    @56
    @27
    @26
    @55
    @56
    @57
    simprbi
    adantr
    @28
    cc0
    cr
    wcel
    @55
    @56
    @168
    wb
    0re
    @58
    cc0
    @21
    leloe
    sylancr
    mpbid
    mpjaodan
    rgen2
    @12
    @25
    vz
    vu
    vv
    @0
    cD
    @9
    @23
    wceq
    @11
    @24
    @4
    @9
    @23
    @10
    fveq2
    eleq2d
    ralxp
    mpbir
    @90
    @48
    @6
    @8
    @13
    wa
    wb
    @91
    @49
    vz
    @4
    @5
    cJ
    @7
    cc
    cncnp
    mp2an
    mpbir2an
end
