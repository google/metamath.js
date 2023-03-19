include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "c0.mm"
include "wceq.mm"
include "ccom.mm"
include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "chash.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "c0g.mm"
include "cmpt.mm"
include "cmnd.mm"
include "eqid.mm"
include "gsumz.mm"
include "syl2anc.mm"
include "adantr.mm"
include "cmhm.mm"
include "mhm0.mm"
include "syl.mm"
include "eqtr4d.mm"
include "mndidcl.mm"
include "ad2antrr.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "csupp.mm"
include "wf.mm"
include "fex.mm"
include "suppimacnv.mm"
include "ssid.mm"
include "syl6eqss.mm"
include "gsumcllem.mm"
include "cbs.mm"
include "mhmf.mm"
include "feqmptd.mm"
include "fveq2.mm"
include "fmptco.mm"
include "mpteq2dv.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "cplusg.mm"
include "cseq.mm"
include "mndcl.mm"
include "3expb.mm"
include "sylan.mm"
include "wf1.mm"
include "wss.mm"
include "f1of1.mm"
include "ad2antll.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "f1ss.mm"
include "f1f.mm"
include "fco.mm"
include "ffvelrnda.mm"
include "cuz.mm"
include "simprl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "mhmlin.mm"
include "coass.mm"
include "fveq1i.mm"
include "fvco3.mm"
include "syl5req.mm"
include "seqhomo.mm"
include "crn.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "sseqtr4d.mm"
include "gsumval3.mm"
include "ccntz.mm"
include "cntzmhm2.mm"
include "rnco2.mm"
include "fveq2i.mm"
include "3sstr4g.mm"
include "eldifi.mm"
include "syl2an.mm"
include "suppssr.mm"
include "3eqtrd.mm"
include "suppss.mm"
include "3eqtr4rd.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fsuppimpd.mm"
include "eqeltrrd.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem gsumzmhm
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  assume gsumzmhm.b: |- B = ( Base ` G )
  assume gsumzmhm.z: |- Z = ( Cntz ` G )
  assume gsumzmhm.g: |- ( ph -> G e. Mnd )
  assume gsumzmhm.h: |- ( ph -> H e. Mnd )
  assume gsumzmhm.a: |- ( ph -> A e. V )
  assume gsumzmhm.k: |- ( ph -> K e. ( G MndHom H ) )
  assume gsumzmhm.f: |- ( ph -> F : A --> B )
  assume gsumzmhm.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzmhm.0: |- .0. = ( 0g ` G )
  assume gsumzmhm.w: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( H gsum ( K o. F ) ) = ( K ` ( G gsum F ) ) )

  proof
    wph
    cF
    ccnv
    cvv
    c.0
    csn
    cdif
    #
    cima
    #
    c0
    wceq
    #
    cH
    cK
    cF
    ccom
    #
    cgsu
    co
    #
    cG
    cF
    cgsu
    co
    #
    cK
    cfv
    #
    wceq
    #
    @1
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @8
    cfz
    co
    #
    @1
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    wa
    #
    wph
    @2
    @7
    wph
    @2
    wa
    #
    cH
    vk
    cA
    cH
    c0g
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    c.0
    cK
    cfv
    #
    @4
    @6
    @15
    @18
    @16
    @19
    wph
    @18
    @16
    wceq
    #
    @2
    wph
    cH
    cmnd
    wcel
    #
    cA
    cV
    wcel
    #
    @20
    gsumzmhm.h
    gsumzmhm.a
    cA
    vk
    cH
    cV
    @16
    @16
    eqid
    #
    gsumz
    syl2anc
    adantr
    wph
    @19
    @16
    wceq
    #
    @2
    wph
    cK
    cG
    cH
    cmhm
    co
    wcel
    #
    @24
    gsumzmhm.k
    cG
    cH
    cK
    @16
    c.0
    gsumzmhm.0
    @23
    mhm0
    syl
    #
    adantr
    eqtr4d
    @15
    @3
    @17
    cH
    cgsu
    @15
    @3
    vk
    cA
    @19
    cmpt
    #
    @17
    @15
    vk
    vx
    cA
    cB
    c.0
    vx
    cv
    #
    cK
    cfv
    #
    @19
    cF
    cK
    wph
    c.0
    cB
    wcel
    #
    @2
    vk
    cv
    cA
    wcel
    wph
    cG
    cmnd
    wcel
    #
    @30
    gsumzmhm.g
    cB
    cG
    c.0
    gsumzmhm.b
    gsumzmhm.0
    mndidcl
    syl
    ad2antrr
    wph
    cA
    cB
    cvv
    vk
    cF
    cV
    @1
    c.0
    gsumzmhm.f
    gsumzmhm.a
    c.0
    cvv
    wcel
    #
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsumzmhm.0
    cG
    c0g
    fvex
    eqeltri
    #
    a1i
    #
    wph
    cF
    c.0
    csupp
    co
    #
    @1
    @1
    wph
    cF
    cvv
    wcel
    #
    @32
    @35
    @1
    wceq
    wph
    cA
    cB
    cF
    wf
    #
    @22
    @36
    gsumzmhm.f
    gsumzmhm.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    @34
    cF
    cvv
    cvv
    c.0
    suppimacnv
    syl2anc
    #
    @1
    ssid
    syl6eqss
    #
    gsumcllem
    #
    wph
    cK
    vx
    cB
    @29
    cmpt
    wceq
    @2
    wph
    vx
    cB
    cH
    cbs
    cfv
    #
    cK
    wph
    @25
    cB
    @41
    cK
    wf
    #
    gsumzmhm.k
    cB
    @41
    cG
    cH
    cK
    gsumzmhm.b
    @41
    eqid
    #
    mhmf
    syl
    #
    feqmptd
    adantr
    @28
    c.0
    cK
    fveq2
    fmptco
    wph
    @27
    @17
    wceq
    @2
    wph
    vk
    cA
    @19
    @16
    @26
    mpteq2dv
    adantr
    eqtrd
    oveq2d
    @15
    @5
    c.0
    cK
    @15
    @5
    cG
    vk
    cA
    c.0
    cmpt
    #
    cgsu
    co
    #
    c.0
    @15
    cF
    @45
    cG
    cgsu
    @40
    oveq2d
    wph
    @46
    c.0
    wceq
    #
    @2
    wph
    @31
    @22
    @47
    gsumzmhm.g
    gsumzmhm.a
    cA
    vk
    cG
    cV
    c.0
    gsumzmhm.0
    gsumz
    syl2anc
    adantr
    eqtrd
    fveq2d
    3eqtr4d
    ex
    wph
    @9
    @13
    @7
    wph
    @9
    wa
    @12
    @7
    vf
    wph
    @9
    @12
    @7
    wph
    @9
    @12
    wa
    #
    wa
    #
    @8
    cG
    cplusg
    cfv
    #
    cF
    @11
    ccom
    #
    c1
    cseq
    cfv
    #
    cK
    cfv
    @8
    cH
    cplusg
    cfv
    #
    @3
    @11
    ccom
    #
    c1
    cseq
    cfv
    @6
    @4
    @49
    vx
    vy
    @50
    @53
    cB
    @51
    @54
    cK
    c1
    @8
    @49
    @31
    @28
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    @28
    @56
    @50
    co
    #
    cB
    wcel
    #
    wph
    @31
    @48
    gsumzmhm.g
    adantr
    #
    @31
    @55
    @57
    @60
    cB
    @50
    cG
    @28
    @56
    gsumzmhm.b
    @50
    eqid
    #
    mndcl
    3expb
    sylan
    @49
    @10
    cB
    @28
    @51
    @49
    @37
    @10
    cA
    @11
    wf
    #
    @10
    cB
    @51
    wf
    #
    wph
    @37
    @48
    gsumzmhm.f
    adantr
    #
    @49
    @10
    cA
    @11
    wf1
    #
    @63
    @49
    @10
    @1
    @11
    wf1
    #
    @1
    cA
    wss
    @66
    @12
    @67
    wph
    @9
    @10
    @1
    @11
    f1of1
    ad2antll
    @49
    cF
    cdm
    #
    @1
    cA
    cF
    @0
    cnvimass
    @49
    @37
    @68
    cA
    wceq
    @65
    cA
    cB
    cF
    fdm
    syl
    syl5sseq
    @10
    @1
    cA
    @11
    f1ss
    syl2anc
    #
    @10
    cA
    @11
    f1f
    syl
    @10
    cA
    cB
    cF
    @11
    fco
    syl2anc
    #
    ffvelrnda
    @49
    @8
    cn
    c1
    cuz
    cfv
    wph
    @9
    @12
    simprl
    #
    nnuz
    syl6eleq
    @49
    @25
    @58
    @59
    cK
    cfv
    @29
    @56
    cK
    cfv
    @53
    co
    wceq
    #
    wph
    @25
    @48
    gsumzmhm.k
    adantr
    #
    @25
    @55
    @57
    @72
    cB
    @50
    @53
    cG
    cH
    cK
    @28
    @56
    gsumzmhm.b
    @62
    @53
    eqid
    #
    mhmlin
    3expb
    sylan
    @49
    @28
    @10
    wcel
    #
    wa
    @28
    @54
    cfv
    @28
    cK
    @51
    ccom
    #
    cfv
    #
    @28
    @51
    cfv
    cK
    cfv
    #
    @28
    @54
    @76
    cK
    cF
    @11
    coass
    fveq1i
    @49
    @64
    @75
    @77
    @78
    wceq
    @70
    @10
    cB
    @28
    cK
    @51
    fvco3
    sylan
    syl5req
    seqhomo
    @49
    @5
    @52
    cK
    @49
    cA
    cB
    @50
    cF
    cG
    @11
    @8
    cV
    @51
    c.0
    csupp
    co
    #
    c.0
    cZ
    gsumzmhm.b
    gsumzmhm.0
    @62
    gsumzmhm.z
    @61
    wph
    @22
    @48
    gsumzmhm.a
    adantr
    #
    @65
    wph
    cF
    crn
    #
    @81
    cZ
    cfv
    wss
    #
    @48
    gsumzmhm.c
    adantr
    #
    @71
    @69
    @49
    @35
    @1
    @11
    crn
    #
    wph
    @35
    @1
    wss
    @48
    @39
    adantr
    #
    @12
    @84
    @1
    wceq
    #
    wph
    @9
    @12
    @10
    @1
    @11
    wfo
    @86
    @10
    @1
    @11
    f1ofo
    @10
    @1
    @11
    forn
    syl
    ad2antll
    #
    sseqtr4d
    @79
    eqid
    gsumval3
    fveq2d
    @49
    cA
    @41
    @53
    @3
    cH
    @11
    @8
    cV
    @54
    @16
    csupp
    co
    #
    @16
    cH
    ccntz
    cfv
    #
    @43
    @23
    @74
    @89
    eqid
    #
    wph
    @21
    @48
    gsumzmhm.h
    adantr
    @80
    @49
    @42
    @37
    cA
    @41
    @3
    wf
    wph
    @42
    @48
    @44
    adantr
    @65
    cA
    cB
    @41
    cK
    cF
    fco
    syl2anc
    #
    @49
    cK
    @81
    cima
    #
    @92
    @89
    cfv
    #
    @3
    crn
    #
    @94
    @89
    cfv
    @49
    @25
    @82
    @92
    @93
    wss
    @73
    @83
    @81
    @81
    cK
    cG
    cH
    @89
    cZ
    gsumzmhm.z
    @90
    cntzmhm2
    syl2anc
    cK
    cF
    rnco2
    #
    @94
    @92
    @89
    @95
    fveq2i
    3sstr4g
    @71
    @69
    @49
    @3
    @16
    csupp
    co
    @1
    @84
    @49
    cA
    @41
    vx
    @3
    @1
    @16
    @91
    @49
    @28
    cA
    @1
    cdif
    wcel
    #
    wa
    #
    @28
    @3
    cfv
    #
    @28
    cF
    cfv
    #
    cK
    cfv
    #
    @19
    @16
    @49
    @37
    @28
    cA
    wcel
    @98
    @100
    wceq
    @96
    @65
    @28
    cA
    @1
    eldifi
    cA
    cB
    @28
    cK
    cF
    fvco3
    syl2an
    @97
    @99
    c.0
    cK
    @49
    cA
    cB
    cvv
    cF
    cV
    @1
    @28
    c.0
    @65
    @85
    @80
    @32
    @49
    @33
    a1i
    suppssr
    fveq2d
    wph
    @24
    @48
    @96
    @26
    ad2antrr
    3eqtrd
    suppss
    @87
    sseqtr4d
    @88
    eqid
    gsumval3
    3eqtr4rd
    expr
    exlimdv
    expimpd
    wph
    @1
    cfn
    wcel
    @2
    @14
    wo
    wph
    @35
    @1
    cfn
    @38
    wph
    cF
    c.0
    gsumzmhm.w
    fsuppimpd
    eqeltrrd
    @1
    vf
    fz1f1o
    syl
    mpjaod
end
