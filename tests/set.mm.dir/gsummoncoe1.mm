include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cn0.mm"
include "cmpt.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "co.mm"
include "cgsu.mm"
include "cco1.mm"
include "csb.mm"
include "cfsupp.mm"
include "cmap.mm"
include "wcel.mm"
include "cvv.mm"
include "wf.mm"
include "r19.21bi.mm"
include "eqid.mm"
include "fmptd.mm"
include "wb.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "nn0ex.mm"
include "elmapg.mm"
include "sylancl.mm"
include "mpbird.mm"
include "c0g.mm"
include "fsuppmapnn0ub.mm"
include "mpd.mm"
include "wa.mm"
include "simpr.mm"
include "ad2antrr.mm"
include "rspcsbela.mm"
include "syl2anc.mm"
include "fvmpts.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "biimpd.mm"
include "ralimdva.mm"
include "cc0.mm"
include "cfz.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfcsb1v.mm"
include "nfeq1.mm"
include "nfim.mm"
include "nfral.mm"
include "nfan.mm"
include "ccmn.mm"
include "crg.mm"
include "ply1ring.mm"
include "ringcmn.mm"
include "3syl.mm"
include "w3a.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "simp2.mm"
include "cmgp.mm"
include "ply1tmcl.mm"
include "syl3anc.mm"
include "3expia.mm"
include "simplr.mm"
include "weq.mm"
include "breq2.mm"
include "csbeq1.mm"
include "imbi12d.mm"
include "cbvral.mm"
include "csbid.mm"
include "eqeq1i.mm"
include "oveq1.mm"
include "csca.mm"
include "ply1sca.mm"
include "syl.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "lmod0vs.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "ex.mm"
include "syl5bi.mm"
include "imim2d.mm"
include "imp.mm"
include "gsummptnn0fz.mm"
include "fveq1d.mm"
include "elfznn0.mm"
include "simpll.mm"
include "adantlr.mm"
include "3jca.mm"
include "sylan2.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "fzfid.mm"
include "coe1fzgsumd.mm"
include "cif.mm"
include "ad3antrrr.mm"
include "expcom.mm"
include "syl11.mm"
include "adantl.mm"
include "coe1tm.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "ring0cl.mm"
include "ifcld.mm"
include "fvmptd.mm"
include "mpteq2da.mm"
include "oveq2d.mm"
include "rspcva.mm"
include "wn.mm"
include "cle.mm"
include "elfz2nn0.mm"
include "cr.mm"
include "nn0re.mm"
include "lelttr.mm"
include "wo.mm"
include "olcd.mm"
include "wne.mm"
include "df-ne.mm"
include "lttri2.mm"
include "syl2anr.mm"
include "syl5bbr.mm"
include "syld.mm"
include "exp4b.mm"
include "expimpd.mm"
include "com23.mm"
include "3adant2.mm"
include "sylbi.mm"
include "expd.mm"
include "syl7.mm"
include "com12.mm"
include "com24.mm"
include "impcom.mm"
include "iffalsed.mm"
include "ringmnd.mm"
include "ovex.mm"
include "gsumz.mm"
include "id.mm"
include "eqcomd.mm"
include "3eqtrd.mm"
include "expr.mm"
include "a2d.mm"
include "com13.mm"
include "mpcom.mm"
include "imp31.mm"
include "pm3.2.mm"
include "nn0red.mm"
include "lenlt.mm"
include "syl2an.mm"
include "syl3anbrc.mm"
include "sylbird.mm"
include "eqcom.mm"
include "ifbi.mm"
include "ax-mp.mm"
include "mpteq2i.mm"
include "syl6eleq.mm"
include "syl5com.mm"
include "gsummpt1n0.mm"
include "syl6com.mm"
include "pm2.61i.mm"
include "rexlimdva.mm"

theorem gsummoncoe1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let vk: setvar k
  let c.ex: class .^
  let c.as: class .*
  let cK: class K
  let cL: class L
  let cX: class X
  let c.0: class .0.
  let vn: setvar n
  let vs: setvar s
  let vx: setvar x
  assume gsummonply1.p: |- P = ( Poly1 ` R )
  assume gsummonply1.b: |- B = ( Base ` P )
  assume gsummonply1.x: |- X = ( var1 ` R )
  assume gsummonply1.e: |- .^ = ( .g ` ( mulGrp ` P ) )
  assume gsummonply1.r: |- ( ph -> R e. Ring )
  assume gsummonply1.k: |- K = ( Base ` R )
  assume gsummonply1.m: |- .* = ( .s ` P )
  assume gsummonply1.0: |- .0. = ( 0g ` R )
  assume gsummonply1.a: |- ( ph -> A. k e. NN0 A e. K )
  assume gsummonply1.f: |- ( ph -> ( k e. NN0 |-> A ) finSupp .0. )
  assume gsummonply1.l: |- ( ph -> L e. NN0 )

  disjoint B k
  disjoint K k
  disjoint k ph
  disjoint .* k
  disjoint L k
  disjoint P k
  disjoint R k
  disjoint .0. k
  disjoint .^ k
  disjoint A n
  disjoint A s
  disjoint A x
  disjoint n s
  disjoint n x
  disjoint s x
  disjoint K n
  disjoint L n
  disjoint L s
  disjoint L x
  disjoint k n
  disjoint k s
  disjoint k x
  disjoint P n
  disjoint P s
  disjoint R n
  disjoint X n
  disjoint X s
  disjoint .0. s
  disjoint .0. n
  disjoint .0. x
  disjoint .^ n
  disjoint .^ s
  disjoint .^ x
  disjoint .* n
  disjoint .* s
  disjoint n ph
  disjoint ph s
  disjoint ph x
  assert |- ( ph -> ( ( coe1 ` ( P gsum ( k e. NN0 |-> ( A .* ( k .^ X ) ) ) ) ) ` L ) = [_ L / k ]_ A )

  proof
    wph
    vs
    cv
    #
    vx
    cv
    #
    clt
    wbr
    #
    @1
    vk
    cn0
    cA
    cmpt
    #
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vs
    cn0
    wrex
    #
    cL
    cP
    vk
    cn0
    cA
    vk
    cv
    #
    cX
    c.ex
    co
    #
    c.as
    co
    #
    cmpt
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    #
    vk
    cL
    cA
    csb
    #
    wceq
    #
    wph
    @3
    c.0
    cfsupp
    wbr
    #
    @8
    gsummonply1.f
    wph
    @3
    cK
    cn0
    cmap
    co
    wcel
    #
    c.0
    cvv
    wcel
    @17
    @8
    wi
    wph
    @18
    cn0
    cK
    @3
    wf
    #
    wph
    vk
    cn0
    cA
    cK
    @3
    wph
    cA
    cK
    wcel
    #
    vk
    cn0
    gsummonply1.a
    r19.21bi
    #
    @3
    eqid
    #
    fmptd
    wph
    cK
    cvv
    wcel
    #
    cn0
    cvv
    wcel
    @18
    @19
    wb
    @23
    wph
    cK
    cR
    cbs
    cfv
    #
    cvv
    gsummonply1.k
    cR
    cbs
    fvex
    eqeltri
    a1i
    nn0ex
    cK
    cn0
    @3
    cvv
    cvv
    elmapg
    sylancl
    mpbird
    c.0
    cR
    c0g
    cfv
    #
    cvv
    gsummonply1.0
    cR
    c0g
    fvex
    eqeltri
    vx
    cK
    vs
    @3
    cvv
    c.0
    fsuppmapnn0ub
    sylancl
    mpd
    wph
    @7
    @16
    vs
    cn0
    wph
    @0
    cn0
    wcel
    #
    wa
    #
    @7
    @2
    vk
    @1
    cA
    csb
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    @16
    @27
    @6
    @30
    vx
    cn0
    @27
    @1
    cn0
    wcel
    #
    wa
    #
    @6
    @30
    @33
    @5
    @29
    @2
    @33
    @4
    @28
    c.0
    @33
    @32
    @28
    cK
    wcel
    #
    @4
    @28
    wceq
    @27
    @32
    simpr
    #
    @33
    @32
    @20
    vk
    cn0
    wral
    #
    @34
    @35
    wph
    @36
    @26
    @32
    gsummonply1.a
    ad2antrr
    vk
    @1
    cn0
    cA
    cK
    rspcsbela
    syl2anc
    vk
    @1
    cA
    cn0
    @3
    cK
    @22
    fvmpts
    syl2anc
    eqeq1d
    imbi2d
    biimpd
    ralimdva
    @27
    @31
    @16
    @27
    @31
    wa
    #
    @14
    cL
    cP
    vk
    cc0
    @0
    cfz
    co
    #
    @11
    cmpt
    cgsu
    co
    #
    cco1
    cfv
    #
    cfv
    cR
    vk
    @38
    cL
    @11
    cco1
    cfv
    #
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    @15
    @37
    cL
    @13
    @40
    @37
    @12
    @39
    cco1
    @37
    cB
    @11
    @0
    vk
    cP
    cP
    c0g
    cfv
    #
    @27
    @31
    vk
    @27
    vk
    nfv
    @30
    vk
    vx
    cn0
    vk
    cn0
    nfcv
    @2
    @29
    vk
    @2
    vk
    nfv
    vk
    @28
    c.0
    vk
    @1
    cA
    nfcsb1v
    nfeq1
    nfim
    #
    nfral
    nfan
    #
    gsummonply1.b
    @45
    eqid
    #
    wph
    cP
    ccmn
    wcel
    #
    @26
    @31
    wph
    cR
    crg
    wcel
    #
    cP
    crg
    wcel
    #
    @49
    gsummonply1.r
    cP
    cR
    gsummonply1.p
    ply1ring
    #
    cP
    ringcmn
    3syl
    ad2antrr
    wph
    @11
    cB
    wcel
    #
    vk
    cn0
    wral
    #
    @26
    @31
    wph
    @36
    @54
    gsummonply1.a
    wph
    @20
    @53
    vk
    cn0
    wph
    @9
    cn0
    wcel
    #
    @20
    @53
    wph
    @55
    @20
    w3a
    #
    @50
    @20
    @55
    @53
    wph
    @55
    @50
    @20
    gsummonply1.r
    3ad2ant1
    wph
    @55
    @20
    simp3
    wph
    @55
    @20
    simp2
    cB
    cA
    @9
    cP
    cR
    c.as
    c.ex
    cK
    cP
    cmgp
    cfv
    #
    cX
    gsummonply1.k
    gsummonply1.p
    gsummonply1.x
    gsummonply1.m
    @57
    eqid
    #
    gsummonply1.e
    gsummonply1.b
    ply1tmcl
    syl3anc
    #
    3expia
    ralimdva
    mpd
    ad2antrr
    wph
    @26
    @31
    simplr
    @27
    @31
    @0
    @9
    clt
    wbr
    #
    @11
    @45
    wceq
    #
    wi
    #
    vk
    cn0
    wral
    #
    @31
    @60
    vk
    @9
    cA
    csb
    #
    c.0
    wceq
    #
    wi
    #
    vk
    cn0
    wral
    @27
    @63
    @30
    @66
    vx
    vk
    cn0
    @46
    @66
    vx
    nfv
    vx
    vk
    weq
    #
    @2
    @60
    @29
    @65
    @1
    @9
    @0
    clt
    breq2
    @67
    @28
    @64
    c.0
    vk
    @1
    @9
    cA
    csbeq1
    eqeq1d
    imbi12d
    cbvral
    @27
    @66
    @62
    vk
    cn0
    @27
    @55
    wa
    #
    @65
    @61
    @60
    @65
    cA
    c.0
    wceq
    #
    @68
    @61
    @64
    cA
    c.0
    vk
    cA
    csbid
    eqeq1i
    @68
    @69
    @61
    @69
    @68
    @11
    c.0
    @10
    c.as
    co
    #
    @45
    cA
    c.0
    @10
    c.as
    oveq1
    @68
    @70
    cP
    csca
    cfv
    #
    c0g
    cfv
    #
    @10
    c.as
    co
    #
    @45
    @68
    c.0
    @72
    @10
    c.as
    wph
    c.0
    @72
    wceq
    @26
    @55
    wph
    c.0
    @25
    @72
    gsummonply1.0
    wph
    cR
    @71
    c0g
    wph
    @50
    cR
    @71
    wceq
    gsummonply1.r
    cP
    cR
    crg
    gsummonply1.p
    ply1sca
    syl
    fveq2d
    syl5eq
    ad2antrr
    oveq1d
    @68
    cP
    clmod
    wcel
    #
    @10
    cP
    cbs
    cfv
    #
    wcel
    #
    @73
    @45
    wceq
    wph
    @74
    @26
    @55
    wph
    @50
    @74
    gsummonply1.r
    cP
    cR
    gsummonply1.p
    ply1lmod
    syl
    ad2antrr
    @68
    @57
    cmnd
    wcel
    #
    @55
    cX
    @75
    wcel
    #
    @76
    wph
    @77
    @26
    @55
    wph
    @50
    @51
    @77
    gsummonply1.r
    @52
    cP
    @57
    @58
    ringmgp
    3syl
    ad2antrr
    @27
    @55
    simpr
    #
    wph
    @78
    @26
    @55
    wph
    @50
    @78
    gsummonply1.r
    @75
    cP
    cR
    cX
    gsummonply1.x
    gsummonply1.p
    @75
    eqid
    #
    vr1cl
    syl
    ad2antrr
    @75
    c.ex
    @57
    @9
    cX
    @75
    cP
    @57
    @58
    @80
    mgpbas
    gsummonply1.e
    mulgnn0cl
    syl3anc
    c.as
    @71
    @72
    @75
    cP
    @10
    @45
    @80
    @71
    eqid
    gsummonply1.m
    @72
    eqid
    @48
    lmod0vs
    syl2anc
    eqtrd
    sylan9eqr
    ex
    syl5bi
    imim2d
    ralimdva
    syl5bi
    imp
    gsummptnn0fz
    fveq2d
    fveq1d
    @37
    vk
    cB
    cP
    cR
    cL
    @11
    @38
    gsummonply1.p
    gsummonply1.b
    wph
    @50
    @26
    @31
    gsummonply1.r
    ad2antrr
    wph
    cL
    cn0
    wcel
    #
    @26
    @31
    gsummonply1.l
    ad2antrr
    @27
    @53
    vk
    @38
    wral
    @31
    @27
    @53
    vk
    @38
    @27
    @9
    @38
    wcel
    #
    wa
    @56
    @53
    @82
    @27
    @55
    @56
    @9
    @0
    elfznn0
    #
    @68
    wph
    @55
    @20
    wph
    @26
    @55
    simpll
    @79
    wph
    @55
    @20
    @26
    @21
    adantlr
    3jca
    sylan2
    @59
    syl
    ralrimiva
    adantr
    @37
    cc0
    @0
    fzfid
    coe1fzgsumd
    @37
    @44
    cR
    vk
    @38
    cL
    @9
    wceq
    #
    cA
    c.0
    cif
    #
    cmpt
    #
    cgsu
    co
    #
    @15
    @37
    @43
    @86
    cR
    cgsu
    @37
    vk
    @38
    @42
    @85
    @47
    @37
    @82
    wa
    #
    vn
    cL
    vn
    vk
    weq
    #
    cA
    c.0
    cif
    #
    @85
    cn0
    @41
    cK
    @88
    @50
    @20
    @55
    @41
    vn
    cn0
    @90
    cmpt
    wceq
    wph
    @50
    @26
    @31
    @82
    gsummonply1.r
    ad3antrrr
    @37
    @82
    @20
    wph
    @82
    @20
    wi
    @26
    @31
    @55
    wph
    @20
    @82
    wph
    @55
    @20
    @21
    expcom
    @83
    syl11
    ad2antrr
    imp
    #
    @82
    @55
    @37
    @83
    adantl
    vn
    cA
    @9
    cP
    cR
    c.as
    c.ex
    cK
    @57
    cX
    c.0
    gsummonply1.0
    gsummonply1.k
    gsummonply1.p
    gsummonply1.x
    gsummonply1.m
    @58
    gsummonply1.e
    coe1tm
    syl3anc
    vn
    cv
    #
    cL
    wceq
    #
    @90
    @85
    wceq
    @88
    @93
    @89
    @84
    cA
    c.0
    @92
    cL
    @9
    eqeq1
    ifbid
    adantl
    wph
    @81
    @26
    @31
    @82
    gsummonply1.l
    ad3antrrr
    @88
    @84
    cA
    c.0
    cK
    @91
    wph
    c.0
    cK
    wcel
    #
    @26
    @31
    @82
    wph
    @50
    @94
    gsummonply1.r
    cK
    cR
    c.0
    gsummonply1.k
    gsummonply1.0
    ring0cl
    syl
    ad3antrrr
    ifcld
    fvmptd
    mpteq2da
    oveq2d
    @0
    cL
    clt
    wbr
    #
    @37
    @87
    @15
    wceq
    #
    wi
    @37
    @95
    @96
    wph
    @26
    @31
    @95
    @96
    wi
    #
    @81
    wph
    @26
    @31
    @97
    wi
    wi
    gsummonply1.l
    @81
    @31
    @26
    wph
    @97
    @81
    @31
    @26
    wph
    @97
    wi
    wi
    #
    @81
    @31
    wa
    @95
    @15
    c.0
    wceq
    #
    wi
    #
    @98
    @30
    @100
    vx
    cL
    cn0
    @1
    cL
    wceq
    #
    @2
    @95
    @29
    @99
    @1
    cL
    @0
    clt
    breq2
    @101
    @28
    @15
    c.0
    vk
    @1
    cL
    cA
    csbeq1
    eqeq1d
    imbi12d
    rspcva
    wph
    @26
    @100
    @97
    wph
    @26
    @100
    @97
    wi
    @27
    @95
    @99
    @96
    wph
    @26
    @95
    @99
    @96
    wi
    wph
    @26
    @95
    wa
    #
    wa
    #
    @99
    @96
    @103
    @99
    wa
    #
    @87
    cR
    vk
    @38
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @15
    @104
    @86
    @105
    cR
    cgsu
    @104
    vk
    @38
    @85
    c.0
    @103
    @99
    vk
    @103
    vk
    nfv
    vk
    @15
    c.0
    vk
    cL
    cA
    nfcsb1v
    nfeq1
    nfan
    @104
    @82
    wa
    @84
    cA
    c.0
    @104
    @82
    @84
    wn
    #
    @103
    @82
    @107
    wi
    #
    @99
    @102
    wph
    @108
    @26
    @95
    wph
    @108
    wi
    @26
    @82
    wph
    @95
    @107
    @82
    @26
    wph
    @95
    @107
    wi
    #
    wi
    wph
    @81
    @82
    @26
    @109
    gsummonply1.l
    @82
    @26
    @81
    @109
    @82
    @55
    @26
    @9
    @0
    cle
    wbr
    #
    w3a
    @26
    @81
    wa
    #
    @109
    wi
    #
    @9
    @0
    elfz2nn0
    @55
    @110
    @112
    @26
    @55
    @110
    @112
    @55
    @111
    @110
    @109
    @55
    @26
    @81
    @110
    @109
    wi
    @55
    @26
    wa
    #
    @81
    @110
    @95
    @107
    @113
    @81
    wa
    #
    @110
    @95
    wa
    #
    @9
    cL
    clt
    wbr
    #
    @107
    @114
    @9
    cr
    wcel
    #
    @0
    cr
    wcel
    #
    cL
    cr
    wcel
    #
    @115
    @116
    wi
    @55
    @117
    @26
    @81
    @9
    nn0re
    #
    ad2antrr
    @113
    @118
    @81
    @26
    @118
    @55
    @0
    nn0re
    #
    adantl
    adantr
    @81
    @119
    @113
    cL
    nn0re
    #
    adantl
    @9
    @0
    cL
    lelttr
    syl3anc
    @114
    @116
    @107
    @114
    @116
    wa
    #
    @107
    cL
    @9
    clt
    wbr
    #
    @116
    wo
    #
    @123
    @116
    @124
    @114
    @116
    simpr
    olcd
    @107
    cL
    @9
    wne
    #
    @123
    @125
    cL
    @9
    df-ne
    @114
    @126
    @125
    wb
    #
    @116
    @81
    @119
    @117
    @127
    @113
    @122
    @55
    @117
    @26
    @120
    adantr
    cL
    @9
    lttri2
    syl2anr
    adantr
    syl5bbr
    mpbird
    ex
    syld
    exp4b
    expimpd
    com23
    imp
    3adant2
    sylbi
    expd
    syl7
    com12
    com24
    imp
    impcom
    adantr
    imp
    iffalsed
    mpteq2da
    oveq2d
    @103
    @106
    c.0
    wceq
    #
    @99
    @103
    cR
    cmnd
    wcel
    #
    @38
    cvv
    wcel
    #
    @128
    wph
    @129
    @102
    wph
    @50
    @129
    gsummonply1.r
    cR
    ringmnd
    syl
    #
    adantr
    cc0
    @0
    cfz
    ovex
    #
    @38
    vk
    cR
    cvv
    c.0
    gsummonply1.0
    gsumz
    sylancl
    adantr
    @99
    c.0
    @15
    wceq
    @103
    @99
    @15
    c.0
    @99
    id
    eqcomd
    adantl
    3eqtrd
    ex
    expr
    a2d
    ex
    com13
    syl
    ex
    com24
    mpcom
    imp31
    com12
    @37
    @95
    wn
    #
    @27
    @133
    wa
    #
    @96
    @27
    @133
    @134
    wi
    @31
    @27
    @133
    pm3.2
    adantr
    @134
    cA
    vk
    @86
    cR
    @38
    cvv
    cL
    c.0
    gsummonply1.0
    wph
    @129
    @26
    @133
    @131
    ad2antrr
    @130
    @134
    @132
    a1i
    @27
    @133
    cL
    @38
    wcel
    #
    @27
    @133
    cL
    @0
    cle
    wbr
    #
    @135
    wph
    @119
    @118
    @136
    @133
    wb
    @26
    wph
    cL
    gsummonply1.l
    nn0red
    @121
    cL
    @0
    lenlt
    syl2an
    @27
    @136
    @135
    @27
    @136
    wa
    @81
    @26
    @136
    @135
    wph
    @81
    @26
    @136
    gsummonply1.l
    ad2antrr
    wph
    @26
    @136
    simplr
    @27
    @136
    simpr
    cL
    @0
    elfz2nn0
    syl3anbrc
    ex
    sylbird
    imp
    vk
    @38
    @85
    @9
    cL
    wceq
    #
    cA
    c.0
    cif
    #
    @84
    @137
    wb
    @85
    @138
    wceq
    cL
    @9
    eqcom
    @84
    @137
    cA
    c.0
    ifbi
    ax-mp
    mpteq2i
    @27
    cA
    @24
    wcel
    #
    vk
    @38
    wral
    @133
    @27
    @139
    vk
    @38
    @82
    @27
    @139
    @82
    @55
    @27
    @139
    @83
    wph
    @55
    @139
    wi
    @26
    wph
    @55
    @139
    wph
    @55
    wa
    cA
    cK
    @24
    @21
    gsummonply1.k
    syl6eleq
    ex
    adantr
    syl5com
    impcom
    ralrimiva
    adantr
    gsummpt1n0
    syl6com
    pm2.61i
    eqtrd
    3eqtrd
    ex
    syld
    rexlimdva
    mpd
end
