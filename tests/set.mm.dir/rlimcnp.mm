include "cmpt.mm"
include "crli.mm"
include "wbr.mm"
include "cc0.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cxp.mm"
include "cres.mm"
include "cmopn.mm"
include "cfv.mm"
include "ccnp.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "clt.mm"
include "wi.mm"
include "wral.mm"
include "crp.mm"
include "wrex.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "wb.mm"
include "rpreccl.mm"
include "adantl.mm"
include "wceq.mm"
include "wne.mm"
include "rpcnne0.mm"
include "recrec.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "simpr.mm"
include "breq1d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rexxfrd.mm"
include "adantr.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "simplr.mm"
include "sselda.mm"
include "adantlr.mm"
include "cr.mm"
include "elrp.mm"
include "ltrec1.mm"
include "syl2anb.mm"
include "ralbidva.mm"
include "rpcn.mm"
include "rpne0.mm"
include "recrecd.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "eleq1.mm"
include "eleq1d.mm"
include "bibi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "mpbird.mm"
include "rpne0d.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "eldifi.mm"
include "cpnf.mm"
include "cico.mm"
include "rge0ssre.mm"
include "ssdifssd.mm"
include "sseldi.mm"
include "cle.mm"
include "cxr.mm"
include "w3a.mm"
include "0re.mm"
include "pnfxr.mm"
include "elico2.mm"
include "mp2an.mm"
include "simp2bi.mm"
include "eldifsni.mm"
include "ne0gt0d.mm"
include "elrpd.mm"
include "syldan.mm"
include "mpbid.mm"
include "breq1.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "imbi12d.mm"
include "ralxfrd.mm"
include "ad2antrr.mm"
include "bitr4d.mm"
include "elsni.mm"
include "subidd.mm"
include "eqtrd.mm"
include "abs00bd.mm"
include "rpgt0.mm"
include "ad2antlr.mm"
include "eqbrtrd.mm"
include "a1d.mm"
include "biantrud.mm"
include "ralunb.mm"
include "syl6bbr.mm"
include "undif1.mm"
include "wss.mm"
include "snssd.mm"
include "ssequn2.mm"
include "sylib.mm"
include "syl5eq.mm"
include "raleqdv.mm"
include "3bitrd.mm"
include "rexbidva.mm"
include "bitrd.mm"
include "nfv.mm"
include "nffvmpt1.mm"
include "nfcv.mm"
include "nfov.mm"
include "nfbr.mm"
include "nfim.mm"
include "oveq1.mm"
include "fveq2.mm"
include "cbvral.mm"
include "ovresd.mm"
include "syl6ss.mm"
include "ax-resscn.mm"
include "0cnd.mm"
include "eqid.mm"
include "cnmetdval.mm"
include "subid1d.mm"
include "3eqtrd.mm"
include "absidd.mm"
include "fvmpt2.mm"
include "fvmptg.mm"
include "oveq12d.mm"
include "syl5bb.mm"
include "rexbidv.mm"
include "fmptd.mm"
include "biantrurd.mm"
include "3bitr2d.mm"
include "rpssre.mm"
include "1red.mm"
include "rlim3.mm"
include "cioo.mm"
include "0xr.mm"
include "0lt1.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "xrltletr.mm"
include "ixxss1.mm"
include "ioorp.mm"
include "sseqtri.mm"
include "ssrexv.mm"
include "ax-mp.mm"
include "ltle.mm"
include "imim1d.mm"
include "ralimdva.mm"
include "reximdva.mm"
include "syl5.mm"
include "ralimdv.mm"
include "sylbid.mm"
include "ralimi.mm"
include "rlim2lt.mm"
include "syl5ibr.mm"
include "impbid.mm"
include "cxmt.mm"
include "cnxmet.mm"
include "xmetres2.mm"
include "sylancr.mm"
include "a1i.mm"
include "cnfldtopn.mm"
include "metcnp2.mm"
include "syl3anc.mm"
include "3bitr4d.mm"
include "crest.mm"
include "metrest.mm"
include "fveq1d.mm"
include "eleq2d.mm"

theorem rlimcnp
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  let cS: class S
  let cJ: class J
  let cK: class K
  let vr: setvar r
  let vw: setvar w
  let vz: setvar z
  let vt: setvar t
  assume rlimcnp.a: |- ( ph -> A C_ ( 0 [,) +oo ) )
  assume rlimcnp.0: |- ( ph -> 0 e. A )
  assume rlimcnp.b: |- ( ph -> B C_ RR+ )
  assume rlimcnp.r: |- ( ( ph /\ x e. A ) -> R e. CC )
  assume rlimcnp.d: |- ( ( ph /\ x e. RR+ ) -> ( x e. A <-> ( 1 / x ) e. B ) )
  assume rlimcnp.c: |- ( x = 0 -> R = C )
  assume rlimcnp.s: |- ( x = ( 1 / y ) -> R = S )
  assume rlimcnp.j: |- J = ( TopOpen ` CCfld )
  assume rlimcnp.k: |- K = ( J |`t A )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint C x
  disjoint C y
  disjoint ph x
  disjoint ph y
  disjoint R y
  disjoint S x
  disjoint r w
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint r t
  disjoint B r
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint B t
  disjoint B z
  disjoint C r
  disjoint C t
  disjoint C z
  disjoint ph r
  disjoint ph t
  disjoint ph z
  disjoint J r
  disjoint J w
  disjoint J z
  disjoint R r
  disjoint R w
  disjoint R z
  disjoint S r
  disjoint S t
  disjoint S z
  assert |- ( ph -> ( ( y e. B |-> S ) ~~>r C <-> ( x e. A |-> R ) e. ( ( K CnP J ) ` 0 ) ) )

  proof
    wph
    vy
    cB
    cS
    cmpt
    cC
    crli
    wbr
    #
    vx
    cA
    cR
    cmpt
    #
    cc0
    cabs
    cmin
    ccom
    #
    cA
    cA
    cxp
    cres
    #
    cmopn
    cfv
    #
    cJ
    ccnp
    co
    #
    cfv
    #
    wcel
    #
    @1
    cc0
    cK
    cJ
    ccnp
    co
    #
    cfv
    #
    wcel
    wph
    vt
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    cS
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    vz
    cv
    #
    clt
    wbr
    #
    wi
    #
    vy
    cB
    wral
    #
    vt
    crp
    wrex
    #
    vz
    crp
    wral
    #
    cA
    cc
    @1
    wf
    #
    vw
    cv
    #
    cc0
    @3
    co
    #
    vr
    cv
    #
    clt
    wbr
    #
    @22
    @1
    cfv
    #
    cc0
    @1
    cfv
    #
    @2
    co
    #
    @15
    clt
    wbr
    #
    wi
    #
    vw
    cA
    wral
    #
    vr
    crp
    wrex
    #
    vz
    crp
    wral
    #
    wa
    #
    @0
    @7
    wph
    @20
    vx
    cv
    #
    @24
    clt
    wbr
    #
    cR
    cC
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
    #
    vx
    cA
    wral
    #
    vr
    crp
    wrex
    #
    vz
    crp
    wral
    @33
    @34
    wph
    @19
    @42
    vz
    crp
    wph
    @15
    crp
    wcel
    #
    wa
    #
    @19
    c1
    @24
    cdiv
    co
    #
    @11
    clt
    wbr
    #
    @16
    wi
    #
    vy
    cB
    wral
    #
    vr
    crp
    wrex
    #
    @42
    wph
    @19
    @49
    wb
    @43
    wph
    @18
    @48
    vt
    vr
    @45
    crp
    crp
    @24
    crp
    wcel
    #
    @45
    crp
    wcel
    wph
    @24
    rpreccl
    adantl
    wph
    @10
    crp
    wcel
    #
    wa
    #
    c1
    @10
    cdiv
    co
    #
    crp
    wcel
    #
    @10
    c1
    @53
    cdiv
    co
    #
    wceq
    #
    @10
    @45
    wceq
    #
    vr
    crp
    wrex
    @51
    @54
    wph
    @10
    rpreccl
    adantl
    @52
    @55
    @10
    @52
    @10
    cc
    wcel
    @10
    cc0
    wne
    wa
    #
    @55
    @10
    wceq
    @51
    @58
    wph
    @10
    rpcnne0
    adantl
    @10
    recrec
    syl
    eqcomd
    @57
    @56
    vr
    @53
    crp
    @24
    @53
    wceq
    @45
    @55
    @10
    @24
    @53
    c1
    cdiv
    oveq2
    eqeq2d
    rspcev
    syl2anc
    wph
    @57
    wa
    #
    @17
    @47
    vy
    cB
    @59
    @12
    @46
    @16
    @59
    @10
    @45
    @11
    clt
    wph
    @57
    simpr
    breq1d
    imbi1d
    ralbidv
    rexxfrd
    adantr
    @44
    @48
    @41
    vr
    crp
    @44
    @50
    wa
    #
    @48
    @40
    vx
    cA
    cc0
    csn
    #
    cdif
    #
    wral
    #
    @40
    vx
    @62
    @61
    cun
    #
    wral
    #
    @41
    @60
    @48
    c1
    @11
    cdiv
    co
    #
    @24
    clt
    wbr
    #
    @16
    wi
    #
    vy
    cB
    wral
    #
    @63
    wph
    @50
    @48
    @69
    wb
    @43
    wph
    @50
    wa
    #
    @47
    @68
    vy
    cB
    @70
    @11
    cB
    wcel
    #
    wa
    #
    @46
    @67
    @16
    @72
    @50
    @11
    crp
    wcel
    #
    @46
    @67
    wb
    #
    wph
    @50
    @71
    simplr
    wph
    @71
    @73
    @50
    wph
    cB
    crp
    @11
    rlimcnp.b
    sselda
    #
    adantlr
    @50
    @24
    cr
    wcel
    cc0
    @24
    clt
    wbr
    wa
    @11
    cr
    wcel
    #
    cc0
    @11
    clt
    wbr
    wa
    @74
    @73
    @24
    elrp
    @11
    elrp
    @24
    @11
    ltrec1
    syl2anb
    syl2anc
    imbi1d
    ralbidva
    adantlr
    wph
    @63
    @69
    wb
    @43
    @50
    wph
    @40
    @68
    vx
    vy
    @66
    @62
    cB
    wph
    @71
    wa
    #
    @66
    cA
    wcel
    #
    @66
    cc0
    wne
    @66
    @62
    wcel
    @77
    @78
    c1
    @66
    cdiv
    co
    #
    cB
    wcel
    #
    @77
    @79
    @11
    cB
    @77
    @73
    @79
    @11
    wceq
    @75
    @73
    @11
    @11
    rpcn
    @11
    rpne0
    recrecd
    syl
    wph
    @71
    simpr
    eqeltrd
    @77
    @66
    crp
    wcel
    #
    @35
    cA
    wcel
    #
    c1
    @35
    cdiv
    co
    #
    cB
    wcel
    #
    wb
    #
    vx
    crp
    wral
    #
    @78
    @80
    wb
    #
    @77
    @73
    @81
    @75
    @11
    rpreccl
    syl
    #
    wph
    @86
    @71
    wph
    @85
    vx
    crp
    rlimcnp.d
    ralrimiva
    adantr
    @85
    @87
    vx
    @66
    crp
    @35
    @66
    wceq
    #
    @82
    @78
    @84
    @80
    @35
    @66
    cA
    eleq1
    @89
    @83
    @79
    cB
    @35
    @66
    c1
    cdiv
    oveq2
    eleq1d
    bibi12d
    rspcv
    sylc
    mpbird
    #
    @77
    @66
    @88
    rpne0d
    @66
    cA
    cc0
    eldifsn
    sylanbrc
    wph
    @35
    @62
    wcel
    #
    wa
    #
    @84
    @35
    c1
    @83
    cdiv
    co
    #
    wceq
    #
    @89
    vy
    cB
    wrex
    @92
    @82
    @84
    @91
    @82
    wph
    @35
    cA
    @61
    eldifi
    adantl
    wph
    @91
    @35
    crp
    wcel
    #
    @85
    @92
    @35
    @92
    cc0
    cpnf
    cico
    co
    #
    cr
    @35
    rge0ssre
    wph
    @62
    @96
    @35
    wph
    cA
    @96
    @61
    rlimcnp.a
    ssdifssd
    sselda
    #
    sseldi
    #
    @92
    @35
    @98
    @92
    @35
    @96
    wcel
    #
    cc0
    @35
    cle
    wbr
    #
    @97
    @99
    @35
    cr
    wcel
    #
    @100
    @35
    cpnf
    clt
    wbr
    #
    cc0
    cr
    wcel
    cpnf
    cxr
    wcel
    @99
    @101
    @100
    @102
    w3a
    wb
    0re
    pnfxr
    cc0
    cpnf
    @35
    elico2
    mp2an
    simp2bi
    #
    syl
    @91
    @35
    cc0
    wne
    wph
    @35
    cA
    cc0
    eldifsni
    adantl
    ne0gt0d
    elrpd
    #
    rlimcnp.d
    syldan
    mpbid
    @92
    @93
    @35
    @92
    @95
    @93
    @35
    wceq
    @104
    @95
    @35
    @35
    rpcn
    @35
    rpne0
    recrecd
    syl
    eqcomd
    @89
    @94
    vy
    @83
    cB
    @11
    @83
    wceq
    @66
    @93
    @35
    @11
    @83
    c1
    cdiv
    oveq2
    eqeq2d
    rspcev
    syl2anc
    @89
    @40
    @68
    wb
    wph
    @89
    @36
    @67
    @39
    @16
    @35
    @66
    @24
    clt
    breq1
    @89
    @38
    @14
    @15
    clt
    @89
    @37
    @13
    cabs
    @89
    cR
    cS
    cC
    cmin
    rlimcnp.s
    oveq1d
    fveq2d
    breq1d
    imbi12d
    adantl
    ralxfrd
    ad2antrr
    bitr4d
    @60
    @63
    @63
    @40
    vx
    @61
    wral
    #
    wa
    @65
    @60
    @105
    @63
    @44
    @105
    @50
    @44
    @40
    vx
    @61
    @44
    @35
    @61
    wcel
    #
    wa
    #
    @39
    @36
    @107
    @38
    cc0
    @15
    clt
    @107
    @37
    @107
    @37
    cC
    cC
    cmin
    co
    #
    cc0
    @107
    cR
    cC
    cC
    cmin
    @107
    @35
    cc0
    wceq
    #
    cR
    cC
    wceq
    @106
    @109
    @44
    @35
    cc0
    elsni
    adantl
    rlimcnp.c
    syl
    oveq1d
    wph
    @108
    cc0
    wceq
    @43
    @106
    wph
    cC
    wph
    cc0
    cA
    wcel
    #
    cR
    cc
    wcel
    #
    vx
    cA
    wral
    #
    cC
    cc
    wcel
    #
    rlimcnp.0
    wph
    @111
    vx
    cA
    rlimcnp.r
    ralrimiva
    #
    @111
    @113
    vx
    cc0
    cA
    @109
    cR
    cC
    cc
    rlimcnp.c
    eleq1d
    rspcv
    sylc
    #
    subidd
    ad2antrr
    eqtrd
    abs00bd
    @43
    cc0
    @15
    clt
    wbr
    wph
    @106
    @15
    rpgt0
    ad2antlr
    eqbrtrd
    a1d
    ralrimiva
    adantr
    biantrud
    @40
    vx
    @62
    @61
    ralunb
    syl6bbr
    @60
    @40
    vx
    @64
    cA
    @60
    @64
    cA
    @61
    cun
    #
    cA
    cA
    @61
    undif1
    @60
    @61
    cA
    wss
    @116
    cA
    wceq
    @60
    cc0
    cA
    wph
    @110
    @43
    @50
    rlimcnp.0
    ad2antrr
    snssd
    @61
    cA
    ssequn2
    sylib
    syl5eq
    raleqdv
    3bitrd
    rexbidva
    bitrd
    ralbidva
    wph
    @32
    @42
    vz
    crp
    wph
    @31
    @41
    vr
    crp
    @31
    @35
    cc0
    @3
    co
    #
    @24
    clt
    wbr
    #
    @35
    @1
    cfv
    #
    @27
    @2
    co
    #
    @15
    clt
    wbr
    #
    wi
    #
    vx
    cA
    wral
    wph
    @41
    @30
    @122
    vw
    vx
    cA
    @25
    @29
    vx
    @25
    vx
    nfv
    vx
    @28
    @15
    clt
    vx
    @26
    @27
    @2
    vx
    cA
    cR
    @22
    nffvmpt1
    vx
    @2
    nfcv
    vx
    cA
    cR
    cc0
    nffvmpt1
    nfov
    vx
    clt
    nfcv
    vx
    @15
    nfcv
    nfbr
    nfim
    @122
    vw
    nfv
    @22
    @35
    wceq
    #
    @25
    @118
    @29
    @121
    @123
    @23
    @117
    @24
    clt
    @22
    @35
    cc0
    @3
    oveq1
    breq1d
    @123
    @28
    @120
    @15
    clt
    @123
    @26
    @119
    @27
    @2
    @22
    @35
    @1
    fveq2
    oveq1d
    breq1d
    imbi12d
    cbvral
    wph
    @122
    @40
    vx
    cA
    wph
    @82
    wa
    #
    @118
    @36
    @121
    @39
    @124
    @117
    @35
    @24
    clt
    @124
    @117
    @35
    cabs
    cfv
    #
    @35
    @124
    @117
    @35
    cc0
    @2
    co
    #
    @35
    cc0
    cmin
    co
    #
    cabs
    cfv
    #
    @125
    @124
    @35
    cc0
    @2
    cA
    wph
    @82
    simpr
    #
    wph
    @110
    @82
    rlimcnp.0
    adantr
    #
    ovresd
    @124
    @35
    cc
    wcel
    cc0
    cc
    wcel
    @126
    @128
    wceq
    wph
    cA
    cc
    @35
    wph
    cA
    cr
    cc
    wph
    cA
    @96
    cr
    rlimcnp.a
    rge0ssre
    syl6ss
    #
    ax-resscn
    syl6ss
    #
    sselda
    #
    @124
    0cnd
    @35
    cc0
    @2
    @2
    eqid
    #
    cnmetdval
    syl2anc
    @124
    @127
    @35
    cabs
    @124
    @35
    @133
    subid1d
    fveq2d
    3eqtrd
    @124
    @35
    wph
    cA
    cr
    @35
    @131
    sselda
    @124
    @99
    @100
    wph
    cA
    @96
    @35
    rlimcnp.a
    sselda
    @103
    syl
    absidd
    eqtrd
    breq1d
    @124
    @120
    @38
    @15
    clt
    @124
    @120
    cR
    cC
    @2
    co
    #
    @38
    @124
    @119
    cR
    @27
    cC
    @2
    @124
    @82
    @111
    @119
    cR
    wceq
    @129
    rlimcnp.r
    vx
    cA
    cR
    cc
    @1
    @1
    eqid
    #
    fvmpt2
    syl2anc
    @124
    @110
    @113
    @27
    cC
    wceq
    @130
    wph
    @113
    @82
    @115
    adantr
    #
    vx
    cc0
    cR
    cC
    cA
    cc
    @1
    rlimcnp.c
    @136
    fvmptg
    syl2anc
    oveq12d
    @124
    @111
    @113
    @135
    @38
    wceq
    rlimcnp.r
    @137
    cR
    cC
    @2
    @134
    cnmetdval
    syl2anc
    eqtrd
    breq1d
    imbi12d
    ralbidva
    syl5bb
    rexbidv
    ralbidv
    wph
    @21
    @33
    wph
    vx
    cA
    cR
    cc
    @1
    rlimcnp.r
    @136
    fmptd
    biantrurd
    3bitr2d
    wph
    @0
    @20
    wph
    @0
    @10
    @11
    cle
    wbr
    #
    @16
    wi
    #
    vy
    cB
    wral
    #
    vt
    c1
    cpnf
    cico
    co
    #
    wrex
    #
    vz
    crp
    wral
    @20
    wph
    vz
    vt
    vy
    cB
    cS
    cC
    c1
    wph
    cS
    cc
    wcel
    #
    vy
    cB
    @77
    @78
    @112
    @143
    @90
    wph
    @112
    @71
    @114
    adantr
    @111
    @143
    vx
    @66
    cA
    @89
    cR
    cS
    cc
    rlimcnp.s
    eleq1d
    rspcv
    sylc
    ralrimiva
    #
    wph
    cB
    crp
    cr
    rlimcnp.b
    rpssre
    syl6ss
    #
    @115
    wph
    1red
    rlim3
    wph
    @142
    @19
    vz
    crp
    @142
    @140
    vt
    crp
    wrex
    #
    wph
    @19
    @141
    crp
    wss
    @142
    @146
    wi
    @141
    cc0
    cpnf
    cioo
    co
    #
    crp
    cc0
    cxr
    wcel
    cc0
    c1
    clt
    wbr
    @141
    @147
    wss
    0xr
    0lt1
    vx
    vy
    vz
    vw
    cc0
    c1
    cpnf
    cico
    clt
    clt
    cle
    cioo
    clt
    vx
    vy
    vz
    df-ioo
    vx
    vy
    vz
    df-ico
    cc0
    c1
    @22
    xrltletr
    ixxss1
    mp2an
    ioorp
    sseqtri
    @140
    vt
    @141
    crp
    ssrexv
    ax-mp
    wph
    @140
    @18
    vt
    crp
    @52
    @139
    @17
    vy
    cB
    @52
    @71
    wa
    #
    @12
    @138
    @16
    @148
    @10
    cr
    wcel
    @76
    @12
    @138
    wi
    @148
    crp
    cr
    @10
    rpssre
    wph
    @51
    @71
    simplr
    sseldi
    @52
    cB
    cr
    @11
    wph
    cB
    cr
    wss
    @51
    @145
    adantr
    sselda
    @10
    @11
    ltle
    syl2anc
    imim1d
    ralimdva
    reximdva
    syl5
    ralimdv
    sylbid
    @20
    @0
    wph
    @18
    vt
    cr
    wrex
    #
    vz
    crp
    wral
    @19
    @149
    vz
    crp
    crp
    cr
    wss
    @19
    @149
    wi
    rpssre
    @18
    vt
    crp
    cr
    ssrexv
    ax-mp
    ralimi
    wph
    vz
    vt
    vy
    cB
    cS
    cC
    @144
    @145
    @115
    rlim2lt
    syl5ibr
    impbid
    wph
    @3
    cA
    cxmt
    cfv
    wcel
    #
    @2
    cc
    cxmt
    cfv
    wcel
    #
    @110
    @7
    @34
    wb
    wph
    @151
    cA
    cc
    wss
    #
    @150
    cnxmet
    @132
    @2
    cA
    cc
    xmetres2
    sylancr
    @151
    wph
    cnxmet
    a1i
    rlimcnp.0
    vz
    vr
    vw
    @3
    @2
    cc0
    @1
    @4
    cJ
    cA
    cc
    @4
    eqid
    #
    cJ
    rlimcnp.j
    cnfldtopn
    #
    metcnp2
    syl3anc
    3bitr4d
    wph
    @9
    @6
    @1
    wph
    cc0
    @8
    @5
    wph
    cK
    @4
    cJ
    ccnp
    wph
    cK
    cJ
    cA
    crest
    co
    #
    @4
    rlimcnp.k
    wph
    @151
    @152
    @155
    @4
    wceq
    cnxmet
    @132
    @2
    @3
    cJ
    @4
    cc
    cA
    @3
    eqid
    @154
    @153
    metrest
    sylancr
    syl5eq
    oveq1d
    fveq1d
    eleq2d
    bitr4d
end
