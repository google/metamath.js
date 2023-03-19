include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "cima.mm"
include "c0.mm"
include "wceq.mm"
include "cgsu.mm"
include "co.mm"
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
include "oppgmnd.mm"
include "syl.mm"
include "oppgid.mm"
include "gsumz.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "csupp.mm"
include "wss.mm"
include "ssid.mm"
include "wf.mm"
include "fex.mm"
include "suppimacnv.mm"
include "sylancl.mm"
include "sseq1d.mm"
include "mpbiri.mm"
include "gsumcllem.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "cplusg.mm"
include "ccom.mm"
include "cseq.mm"
include "crn.mm"
include "csubmnd.mm"
include "cmrc.mm"
include "cuz.mm"
include "simprl.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "wfo.mm"
include "wfn.mm"
include "ffn.mm"
include "dffn4.mm"
include "sylib.mm"
include "fof.mm"
include "3syl.mm"
include "cacs.mm"
include "cmre.mm"
include "submacs.mm"
include "acsmre.mm"
include "eqid.mm"
include "frn.mm"
include "mrcssidd.mm"
include "fssd.mm"
include "wf1.mm"
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
include "mrccl.mm"
include "oppgsubm.mm"
include "submcl.mm"
include "3expb.mm"
include "sylan.mm"
include "cress.mm"
include "ccmn.mm"
include "cntzspan.mm"
include "wb.mm"
include "submcmn2.mm"
include "mpbid.mm"
include "sselda.mm"
include "cntzi.mm"
include "oppgplus.mm"
include "syl6reqr.mm"
include "anasss.mm"
include "seqfeq4.mm"
include "ccntz.mm"
include "oppgbas.mm"
include "oppgcntz.mm"
include "syl6sseq.mm"
include "wi.mm"
include "suppssdm.mm"
include "syl6eqssr.mm"
include "adantl.mm"
include "eqcom.mm"
include "biimpi.mm"
include "sseqtr4d.mm"
include "mpcom.mm"
include "f1ofo.mm"
include "forn.mm"
include "sseq2d.mm"
include "mpbird.mm"
include "gsumval3.mm"
include "expr.mm"
include "exlimdv.mm"
include "expimpd.mm"
include "cfn.mm"
include "wo.mm"
include "fsuppimpd.mm"
include "eqeltrrd.mm"
include "fz1f1o.mm"
include "mpjaod.mm"

theorem gsumzoppg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cO: class O
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume gsumzoppg.b: |- B = ( Base ` G )
  assume gsumzoppg.0: |- .0. = ( 0g ` G )
  assume gsumzoppg.z: |- Z = ( Cntz ` G )
  assume gsumzoppg.o: |- O = ( oppG ` G )
  assume gsumzoppg.g: |- ( ph -> G e. Mnd )
  assume gsumzoppg.a: |- ( ph -> A e. V )
  assume gsumzoppg.f: |- ( ph -> F : A --> B )
  assume gsumzoppg.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzoppg.n: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( O gsum F ) = ( G gsum F ) )

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
    cO
    cF
    cgsu
    co
    #
    cG
    cF
    cgsu
    co
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
    @6
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
    @5
    wph
    @2
    wa
    #
    cO
    vk
    cA
    c.0
    cmpt
    #
    cgsu
    co
    #
    cG
    @14
    cgsu
    co
    #
    @3
    @4
    wph
    @15
    @16
    wceq
    @2
    wph
    @15
    c.0
    @16
    wph
    cO
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
    wph
    cG
    cmnd
    wcel
    #
    @17
    gsumzoppg.g
    cG
    cO
    gsumzoppg.o
    oppgmnd
    #
    syl
    gsumzoppg.a
    cA
    vk
    cO
    cV
    c.0
    cG
    cO
    c.0
    gsumzoppg.o
    gsumzoppg.0
    oppgid
    #
    gsumz
    syl2anc
    wph
    @19
    @18
    @16
    c.0
    wceq
    gsumzoppg.g
    gsumzoppg.a
    cA
    vk
    cG
    cV
    c.0
    gsumzoppg.0
    gsumz
    syl2anc
    eqtr4d
    adantr
    @13
    cF
    @14
    cO
    cgsu
    wph
    cA
    cB
    cvv
    vk
    cF
    cV
    @1
    c.0
    gsumzoppg.f
    gsumzoppg.a
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
    gsumzoppg.0
    cG
    c0g
    fvex
    eqeltri
    #
    a1i
    wph
    cF
    c.0
    csupp
    co
    #
    @1
    wss
    #
    @1
    @1
    wss
    #
    @1
    ssid
    #
    wph
    @24
    @1
    @1
    wph
    cF
    cvv
    wcel
    #
    @22
    @24
    @1
    wceq
    wph
    cA
    cB
    cF
    wf
    #
    @18
    @28
    gsumzoppg.f
    gsumzoppg.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    @23
    cF
    cvv
    cvv
    c.0
    suppimacnv
    sylancl
    #
    sseq1d
    #
    mpbiri
    #
    gsumcllem
    #
    oveq2d
    @13
    cF
    @14
    cG
    cgsu
    @33
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
    cO
    cplusg
    cfv
    #
    cF
    @9
    ccom
    #
    c1
    cseq
    cfv
    @6
    cG
    cplusg
    cfv
    #
    @37
    c1
    cseq
    cfv
    @3
    @4
    @35
    vx
    vy
    @36
    @38
    cF
    crn
    #
    cG
    csubmnd
    cfv
    #
    cmrc
    cfv
    #
    cfv
    #
    @37
    c1
    @6
    @35
    @6
    cn
    c1
    cuz
    cfv
    wph
    @7
    @10
    simprl
    #
    nnuz
    syl6eleq
    @35
    @8
    @42
    vx
    cv
    #
    @37
    @35
    cA
    @42
    cF
    wf
    @8
    cA
    @9
    wf
    #
    @8
    @42
    @37
    wf
    @35
    cA
    @39
    @42
    cF
    @35
    @29
    cA
    @39
    cF
    wfo
    #
    cA
    @39
    cF
    wf
    wph
    @29
    @34
    gsumzoppg.f
    adantr
    #
    @29
    cF
    cA
    wfn
    @46
    cA
    cB
    cF
    ffn
    cA
    cF
    dffn4
    sylib
    cA
    @39
    cF
    fof
    3syl
    @35
    @40
    @39
    @41
    cB
    @35
    @19
    @40
    cB
    cacs
    cfv
    wcel
    @40
    cB
    cmre
    cfv
    wcel
    #
    wph
    @19
    @34
    gsumzoppg.g
    adantr
    #
    cB
    cG
    gsumzoppg.b
    submacs
    @40
    cB
    acsmre
    3syl
    #
    @41
    eqid
    #
    @35
    @29
    @39
    cB
    wss
    #
    @47
    cA
    cB
    cF
    frn
    syl
    #
    mrcssidd
    fssd
    @35
    @8
    cA
    @9
    wf1
    #
    @45
    @35
    @8
    @1
    @9
    wf1
    #
    @1
    cA
    wss
    #
    @54
    @10
    @55
    wph
    @7
    @8
    @1
    @9
    f1of1
    ad2antll
    #
    @35
    cF
    cdm
    #
    @1
    cA
    cF
    @0
    cnvimass
    @35
    @29
    @58
    cA
    wceq
    #
    @47
    cA
    cB
    cF
    fdm
    #
    syl
    syl5sseq
    @8
    @1
    cA
    @9
    f1ss
    #
    syl2anc
    @8
    cA
    @9
    f1f
    syl
    @8
    cA
    @42
    cF
    @9
    fco
    syl2anc
    ffvelrnda
    @35
    @42
    cO
    csubmnd
    cfv
    #
    wcel
    #
    @44
    @42
    wcel
    #
    vy
    cv
    #
    @42
    wcel
    #
    wa
    @44
    @65
    @36
    co
    #
    @42
    wcel
    #
    @35
    @42
    @40
    @62
    @35
    @48
    @52
    @42
    @40
    wcel
    #
    @50
    @53
    @40
    @39
    @41
    cB
    @51
    mrccl
    syl2anc
    #
    cG
    cO
    gsumzoppg.o
    oppgsubm
    syl6eleq
    @63
    @64
    @66
    @68
    @36
    @42
    cO
    @44
    @65
    @36
    eqid
    #
    submcl
    3expb
    sylan
    @35
    @64
    @66
    @67
    @44
    @65
    @38
    co
    #
    wceq
    @35
    @64
    wa
    #
    @66
    wa
    @72
    @65
    @44
    @38
    co
    #
    @67
    @73
    @44
    @42
    cZ
    cfv
    #
    wcel
    @66
    @72
    @74
    wceq
    @35
    @42
    @75
    @44
    @35
    cG
    @42
    cress
    co
    #
    ccmn
    wcel
    #
    @42
    @75
    wss
    #
    @35
    @19
    @39
    @39
    cZ
    cfv
    #
    wss
    #
    @77
    @49
    wph
    @80
    @34
    gsumzoppg.c
    adantr
    #
    @39
    cG
    @76
    @41
    cZ
    gsumzoppg.z
    @51
    @76
    eqid
    #
    cntzspan
    syl2anc
    @35
    @69
    @77
    @78
    wb
    @70
    @42
    cG
    @76
    cZ
    @82
    gsumzoppg.z
    submcmn2
    syl
    mpbid
    sselda
    @38
    @42
    cG
    @44
    @65
    cZ
    @38
    eqid
    #
    gsumzoppg.z
    cntzi
    sylan
    @38
    @36
    cG
    cO
    @44
    @65
    @83
    gsumzoppg.o
    @71
    oppgplus
    syl6reqr
    anasss
    seqfeq4
    @35
    cA
    cB
    @36
    cF
    cO
    @9
    @6
    cV
    @37
    c.0
    csupp
    co
    #
    c.0
    cO
    ccntz
    cfv
    #
    cB
    cG
    cO
    gsumzoppg.o
    gsumzoppg.b
    oppgbas
    @21
    @71
    @85
    eqid
    @35
    @19
    @17
    @49
    @20
    syl
    wph
    @18
    @34
    gsumzoppg.a
    adantr
    #
    @47
    @35
    @39
    @79
    @39
    @85
    cfv
    @81
    @39
    cG
    cO
    cZ
    gsumzoppg.o
    gsumzoppg.z
    oppgcntz
    syl6sseq
    @43
    @35
    @55
    @56
    @54
    @57
    wph
    @56
    @34
    @29
    wph
    @56
    gsumzoppg.f
    @29
    @59
    wph
    @56
    wi
    @60
    @59
    wph
    @56
    @59
    wph
    wa
    @1
    @58
    cA
    wph
    @1
    @58
    wss
    @59
    wph
    @1
    @24
    @58
    @30
    cF
    c.0
    suppssdm
    syl6eqssr
    adantl
    @59
    cA
    @58
    wceq
    #
    wph
    @59
    @87
    @58
    cA
    eqcom
    biimpi
    adantr
    sseqtr4d
    ex
    syl
    mpcom
    adantr
    @61
    syl2anc
    #
    @35
    @24
    @9
    crn
    #
    wss
    #
    @25
    @35
    @25
    @26
    @27
    wph
    @25
    @26
    wb
    @34
    @31
    adantr
    mpbiri
    @10
    @90
    @25
    wb
    wph
    @7
    @10
    @89
    @1
    @24
    @10
    @8
    @1
    @9
    wfo
    @89
    @1
    wceq
    @8
    @1
    @9
    f1ofo
    @8
    @1
    @9
    forn
    syl
    sseq2d
    ad2antll
    #
    mpbird
    @84
    eqid
    #
    gsumval3
    @35
    cA
    cB
    @38
    cF
    cG
    @9
    @6
    cV
    @84
    c.0
    cZ
    gsumzoppg.b
    gsumzoppg.0
    @83
    gsumzoppg.z
    @49
    @86
    @47
    @81
    @43
    @88
    @35
    @90
    @25
    wph
    @25
    @34
    @32
    adantr
    @91
    mpbird
    @92
    gsumval3
    3eqtr4d
    expr
    exlimdv
    expimpd
    wph
    @1
    cfn
    wcel
    @2
    @12
    wo
    wph
    @24
    @1
    cfn
    @30
    wph
    cF
    c.0
    gsumzoppg.n
    fsuppimpd
    eqeltrrd
    @1
    vf
    fz1f1o
    syl
    mpjaod
end
