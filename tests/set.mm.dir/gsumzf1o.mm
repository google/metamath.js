include "csupp.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cgsu.mm"
include "ccom.mm"
include "chash.mm"
include "cfv.mm"
include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "cv.mm"
include "wf1o.mm"
include "wex.mm"
include "wa.mm"
include "cmpt.mm"
include "cmnd.mm"
include "gsumz.mm"
include "syl2anc.mm"
include "cvv.mm"
include "wf1.mm"
include "f1of1.mm"
include "syl.mm"
include "f1dmex.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "gsumcllem.mm"
include "oveq2d.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "feqmptd.mm"
include "eqidd.mm"
include "fmptco.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "cplusg.mm"
include "cseq.mm"
include "ccnv.mm"
include "coass.mm"
include "cid.mm"
include "cres.mm"
include "f1ococnv2.mm"
include "coeq1d.mm"
include "ad2antll.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "f1ss.mm"
include "f1f.mm"
include "fcoi2.mm"
include "3syl.mm"
include "eqtrd.mm"
include "syl5reqr.mm"
include "coeq2d.mm"
include "syl6eqr.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "eqid.mm"
include "crn.mm"
include "simprl.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "syl5sseqr.mm"
include "gsumval3.mm"
include "fco.mm"
include "rncoss.mm"
include "cntzidss.mm"
include "sylancl.mm"
include "f1ocnv.mm"
include "f1co.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "fex.mm"
include "suppimacnv.mm"
include "eqcomd.mm"
include "3sstr4d.mm"
include "imass2.mm"
include "cnvco.mm"
include "imaeq1i.mm"
include "imaco.mm"
include "eqtri.mm"
include "rnco2.mm"
include "3sstr4g.mm"
include "wb.mm"
include "f1oexrnex.mm"
include "coexg.mm"
include "sseq1d.mm"
include "mpbird.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cfn.mm"
include "wo.mm"
include "wfun.mm"
include "fsuppimp.mm"
include "simprd.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem gsumzf1o
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cH: class H
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let cW: class W
  assume gsumzcl.b: |- B = ( Base ` G )
  assume gsumzcl.0: |- .0. = ( 0g ` G )
  assume gsumzcl.z: |- Z = ( Cntz ` G )
  assume gsumzcl.g: |- ( ph -> G e. Mnd )
  assume gsumzcl.a: |- ( ph -> A e. V )
  assume gsumzcl.f: |- ( ph -> F : A --> B )
  assume gsumzcl.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzcl.w: |- ( ph -> F finSupp .0. )
  assume gsumzf1o.h: |- ( ph -> H : C -1-1-onto-> A )


  assert |- ( ph -> ( G gsum F ) = ( G gsum ( F o. H ) ) )

  proof
    wph
    cF
    c.0
    csupp
    co
    #
    c0
    wceq
    #
    cG
    cF
    cgsu
    co
    #
    cG
    cF
    cH
    ccom
    #
    cgsu
    co
    #
    wceq
    #
    @0
    chash
    cfv
    #
    cn
    wcel
    #
    c1
    @6
    cfz
    co
    #
    @0
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
    @1
    @5
    wph
    @1
    wa
    #
    cG
    vk
    cA
    c.0
    cmpt
    #
    cgsu
    co
    #
    cG
    vx
    cC
    c.0
    cmpt
    #
    cgsu
    co
    #
    @2
    @4
    wph
    @15
    @17
    wceq
    @1
    wph
    @15
    c.0
    @17
    wph
    cG
    cmnd
    wcel
    #
    cA
    cV
    wcel
    #
    @15
    c.0
    wceq
    gsumzcl.g
    gsumzcl.a
    cA
    vk
    cG
    cV
    c.0
    gsumzcl.0
    gsumz
    syl2anc
    wph
    @18
    cC
    cvv
    wcel
    #
    @17
    c.0
    wceq
    gsumzcl.g
    wph
    cC
    cA
    cH
    wf1
    #
    @19
    @20
    wph
    cC
    cA
    cH
    wf1o
    #
    @21
    gsumzf1o.h
    cC
    cA
    cH
    f1of1
    syl
    gsumzcl.a
    cC
    cA
    cV
    cH
    f1dmex
    syl2anc
    #
    cC
    vx
    cG
    cvv
    c.0
    gsumzcl.0
    gsumz
    syl2anc
    eqtr4d
    adantr
    @13
    cF
    @14
    cG
    cgsu
    wph
    cA
    cB
    cvv
    vk
    cF
    cV
    @0
    c.0
    gsumzcl.f
    gsumzcl.a
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
    gsumzcl.0
    cG
    c0g
    fvex
    eqeltri
    #
    a1i
    @0
    @0
    wss
    #
    wph
    @0
    ssid
    #
    a1i
    gsumcllem
    #
    oveq2d
    @13
    @3
    @16
    cG
    cgsu
    @13
    vx
    vk
    cC
    cA
    vx
    cv
    #
    cH
    cfv
    #
    c.0
    c.0
    cH
    cF
    @13
    cC
    cA
    @29
    cH
    wph
    cC
    cA
    cH
    wf
    #
    @1
    wph
    @22
    @31
    gsumzf1o.h
    cC
    cA
    cH
    f1of
    syl
    #
    adantr
    #
    ffvelrnda
    @13
    vx
    cC
    cA
    cH
    @33
    feqmptd
    @28
    vk
    cv
    @30
    wceq
    c.0
    eqidd
    fmptco
    oveq2d
    3eqtr4d
    ex
    wph
    @7
    @11
    @5
    wph
    @7
    wa
    @10
    @5
    vf
    wph
    @7
    @10
    @5
    wph
    @7
    @10
    wa
    #
    wa
    #
    @6
    cG
    cplusg
    cfv
    #
    cF
    @9
    ccom
    #
    c1
    cseq
    #
    cfv
    @6
    @36
    @3
    cH
    ccnv
    #
    @9
    ccom
    #
    ccom
    #
    c1
    cseq
    #
    cfv
    @2
    @4
    @35
    @6
    @38
    @42
    @35
    @37
    @41
    @36
    c1
    @35
    @37
    cF
    cH
    @40
    ccom
    #
    ccom
    @41
    @35
    @9
    @43
    cF
    @35
    @43
    cH
    @39
    ccom
    #
    @9
    ccom
    #
    @9
    cH
    @39
    @9
    coass
    @35
    @45
    cid
    cA
    cres
    #
    @9
    ccom
    #
    @9
    @35
    @44
    @46
    @9
    @35
    @22
    @44
    @46
    wceq
    wph
    @22
    @34
    gsumzf1o.h
    adantr
    cC
    cA
    cH
    f1ococnv2
    syl
    coeq1d
    @35
    @8
    cA
    @9
    wf1
    #
    @8
    cA
    @9
    wf
    @47
    @9
    wceq
    @35
    @8
    @0
    @9
    wf1
    #
    @0
    cA
    wss
    #
    @48
    @10
    @49
    wph
    @7
    @8
    @0
    @9
    f1of1
    ad2antll
    wph
    @50
    @34
    wph
    cF
    cdm
    #
    @0
    cA
    cF
    c.0
    suppssdm
    wph
    cA
    cB
    cF
    wf
    #
    @51
    cA
    wceq
    gsumzcl.f
    cA
    cB
    cF
    fdm
    syl
    syl5sseq
    adantr
    @8
    @0
    cA
    @9
    f1ss
    syl2anc
    #
    @8
    cA
    @9
    f1f
    @8
    cA
    @9
    fcoi2
    3syl
    eqtrd
    syl5reqr
    coeq2d
    cF
    cH
    @40
    coass
    syl6eqr
    seqeq3d
    fveq1d
    @35
    cA
    cB
    @36
    cF
    cG
    @9
    @6
    cV
    @37
    c.0
    csupp
    co
    #
    c.0
    cZ
    gsumzcl.b
    gsumzcl.0
    @36
    eqid
    #
    gsumzcl.z
    wph
    @18
    @34
    gsumzcl.g
    adantr
    #
    wph
    @19
    @34
    gsumzcl.a
    adantr
    wph
    @52
    @34
    gsumzcl.f
    adantr
    wph
    cF
    crn
    #
    @57
    cZ
    cfv
    wss
    #
    @34
    gsumzcl.c
    adantr
    wph
    @7
    @10
    simprl
    #
    @53
    @35
    @0
    @0
    @9
    crn
    #
    @27
    @10
    @60
    @0
    wceq
    #
    wph
    @7
    @10
    @8
    @0
    @9
    wfo
    @61
    @8
    @0
    @9
    f1ofo
    @8
    @0
    @9
    forn
    syl
    ad2antll
    #
    syl5sseqr
    @54
    eqid
    gsumval3
    @35
    cC
    cB
    @36
    @3
    cG
    @40
    @6
    cvv
    @41
    c.0
    csupp
    co
    #
    c.0
    cZ
    gsumzcl.b
    gsumzcl.0
    @55
    gsumzcl.z
    @56
    wph
    @20
    @34
    @23
    adantr
    wph
    cC
    cB
    @3
    wf
    #
    @34
    wph
    @52
    @31
    @64
    gsumzcl.f
    @32
    cC
    cA
    cB
    cF
    cH
    fco
    syl2anc
    adantr
    wph
    @3
    crn
    #
    @65
    cZ
    cfv
    wss
    #
    @34
    wph
    @58
    @65
    @57
    wss
    @66
    gsumzcl.c
    cF
    cH
    rncoss
    @57
    @65
    cG
    cZ
    gsumzcl.z
    cntzidss
    sylancl
    adantr
    @59
    @35
    cA
    cC
    @39
    wf1
    #
    @48
    @8
    cC
    @40
    wf1
    wph
    @67
    @34
    wph
    @22
    cA
    cC
    @39
    wf1o
    @67
    gsumzf1o.h
    cC
    cA
    cH
    f1ocnv
    cA
    cC
    @39
    f1of1
    3syl
    adantr
    @53
    @8
    cA
    cC
    @39
    @9
    f1co
    syl2anc
    @35
    @3
    c.0
    csupp
    co
    #
    @40
    crn
    #
    wss
    #
    @3
    ccnv
    #
    cvv
    c.0
    csn
    cdif
    #
    cima
    #
    @69
    wss
    #
    @35
    @39
    cF
    ccnv
    #
    @72
    cima
    #
    cima
    #
    @39
    @60
    cima
    #
    @73
    @69
    @35
    @76
    @60
    wss
    @77
    @78
    wss
    @35
    @0
    @0
    @76
    @60
    @26
    @35
    @27
    a1i
    wph
    @76
    @0
    wceq
    @34
    wph
    @0
    @76
    wph
    cF
    cvv
    wcel
    #
    @24
    @0
    @76
    wceq
    wph
    @52
    @19
    @79
    gsumzcl.f
    gsumzcl.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    #
    @25
    cF
    cvv
    cvv
    c.0
    suppimacnv
    sylancl
    eqcomd
    adantr
    @62
    3sstr4d
    @76
    @60
    @39
    imass2
    syl
    @73
    @39
    @75
    ccom
    #
    @72
    cima
    @77
    @71
    @81
    @72
    cF
    cH
    cnvco
    imaeq1i
    @39
    @75
    @72
    imaco
    eqtri
    @39
    @9
    rnco2
    3sstr4g
    wph
    @70
    @74
    wb
    @34
    wph
    @68
    @73
    @69
    wph
    @3
    cvv
    wcel
    #
    @24
    @68
    @73
    wceq
    wph
    @79
    cH
    cvv
    wcel
    #
    @82
    @80
    wph
    @22
    @19
    @83
    gsumzf1o.h
    gsumzcl.a
    cC
    cA
    cH
    cV
    f1oexrnex
    syl2anc
    cF
    cH
    cvv
    cvv
    coexg
    syl2anc
    @25
    @3
    cvv
    cvv
    c.0
    suppimacnv
    sylancl
    sseq1d
    adantr
    mpbird
    @63
    eqid
    gsumval3
    3eqtr4d
    expr
    exlimdv
    expimpd
    wph
    cF
    c.0
    cfsupp
    wbr
    #
    @0
    cfn
    wcel
    #
    @1
    @12
    wo
    gsumzcl.w
    @84
    cF
    wfun
    @85
    cF
    c.0
    fsuppimp
    simprd
    @0
    vf
    fz1f1o
    3syl
    mpjaod
end
