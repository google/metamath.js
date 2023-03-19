include "cv.mm"
include "wcel.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "cres.mm"
include "crn.mm"
include "csubmnd.mm"
include "cmrc.mm"
include "cvv.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "fsuppmptif.mm"
include "cmre.mm"
include "wss.mm"
include "cmnd.mm"
include "cacs.mm"
include "submacs.mm"
include "acsmre.mm"
include "3syl.mm"
include "wf.mm"
include "frn.mm"
include "syl.mm"
include "eqid.mm"
include "mrccl.mm"
include "syl2anc.mm"
include "cress.mm"
include "ccmn.mm"
include "cntzspan.mm"
include "wb.mm"
include "submcmn2.mm"
include "mpbid.mm"
include "wa.mm"
include "mrcssidd.mm"
include "adantr.mm"
include "wfn.mm"
include "ffn.mm"
include "fnfvelrn.mm"
include "sylan.mm"
include "sseldd.mm"
include "subm0cl.mm"
include "ifcld.mm"
include "fmptd.mm"
include "gsumzadd.mm"
include "feqmptd.mm"
include "wceq.mm"
include "iftrue.mm"
include "adantl.mm"
include "wn.mm"
include "wi.mm"
include "cin.mm"
include "c0.mm"
include "noel.mm"
include "eleq2.mm"
include "mtbiri.mm"
include "elin.mm"
include "sylnib.mm"
include "imnan.mm"
include "sylibr.mm"
include "imp.mm"
include "iffalsed.mm"
include "oveq12d.mm"
include "ffvelrnda.mm"
include "mndrid.mm"
include "syldan.mm"
include "eqtrd.mm"
include "con2d.mm"
include "mndlid.mm"
include "wo.mm"
include "cun.mm"
include "eleq2d.mm"
include "elun.mm"
include "syl6bb.mm"
include "biimpa.mm"
include "mpjaodan.mm"
include "mpteq2dva.mm"
include "eqtr4d.mm"
include "mndidcl.mm"
include "eqidd.mm"
include "offval2.mm"
include "oveq2d.mm"
include "reseq1d.mm"
include "ssun1.mm"
include "syl5sseqr.mm"
include "mpteq2ia.mm"
include "resmpt.mm"
include "3eqtr4a.mm"
include "cntzidss.mm"
include "cdif.mm"
include "eldifn.mm"
include "suppss2.mm"
include "gsumzres.mm"
include "ssun2.mm"
include "3eqtr4d.mm"

theorem gsumzsplit
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let cF: class F
  let cG: class G
  let cV: class V
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  assume gsumzsplit.b: |- B = ( Base ` G )
  assume gsumzsplit.0: |- .0. = ( 0g ` G )
  assume gsumzsplit.p: |- .+ = ( +g ` G )
  assume gsumzsplit.z: |- Z = ( Cntz ` G )
  assume gsumzsplit.g: |- ( ph -> G e. Mnd )
  assume gsumzsplit.a: |- ( ph -> A e. V )
  assume gsumzsplit.f: |- ( ph -> F : A --> B )
  assume gsumzsplit.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzsplit.w: |- ( ph -> F finSupp .0. )
  assume gsumzsplit.i: |- ( ph -> ( C i^i D ) = (/) )
  assume gsumzsplit.u: |- ( ph -> A = ( C u. D ) )


  assert |- ( ph -> ( G gsum F ) = ( ( G gsum ( F |` C ) ) .+ ( G gsum ( F |` D ) ) ) )

  proof
    wph
    cG
    vk
    cA
    vk
    cv
    #
    cC
    wcel
    #
    @0
    cF
    cfv
    #
    c.0
    cif
    #
    cmpt
    #
    vk
    cA
    @0
    cD
    wcel
    #
    @2
    c.0
    cif
    #
    cmpt
    #
    c.pl
    cof
    co
    #
    cgsu
    co
    cG
    @4
    cgsu
    co
    #
    cG
    @7
    cgsu
    co
    #
    c.pl
    co
    cG
    cF
    cgsu
    co
    cG
    cF
    cC
    cres
    #
    cgsu
    co
    #
    cG
    cF
    cD
    cres
    #
    cgsu
    co
    #
    c.pl
    co
    wph
    cA
    cB
    c.pl
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
    @4
    cG
    @7
    cV
    c.0
    cZ
    gsumzsplit.b
    gsumzsplit.0
    gsumzsplit.p
    gsumzsplit.z
    gsumzsplit.g
    gsumzsplit.a
    wph
    cA
    cB
    cC
    vk
    cF
    cV
    cvv
    c.0
    gsumzsplit.f
    gsumzsplit.a
    c.0
    cvv
    wcel
    wph
    c.0
    cG
    c0g
    cfv
    cvv
    gsumzsplit.0
    cG
    c0g
    fvex
    eqeltri
    a1i
    #
    gsumzsplit.w
    fsuppmptif
    #
    wph
    cA
    cB
    cD
    vk
    cF
    cV
    cvv
    c.0
    gsumzsplit.f
    gsumzsplit.a
    @19
    gsumzsplit.w
    fsuppmptif
    #
    wph
    @16
    cB
    cmre
    cfv
    wcel
    #
    @15
    cB
    wss
    #
    @18
    @16
    wcel
    #
    wph
    cG
    cmnd
    wcel
    #
    @16
    cB
    cacs
    cfv
    wcel
    @22
    gsumzsplit.g
    cB
    cG
    gsumzsplit.b
    submacs
    @16
    cB
    acsmre
    3syl
    #
    wph
    cA
    cB
    cF
    wf
    #
    @23
    gsumzsplit.f
    cA
    cB
    cF
    frn
    syl
    #
    @16
    @15
    @17
    cB
    @17
    eqid
    #
    mrccl
    syl2anc
    #
    wph
    cG
    @18
    cress
    co
    #
    ccmn
    wcel
    #
    @18
    @18
    cZ
    cfv
    wss
    #
    wph
    @25
    @15
    @15
    cZ
    cfv
    wss
    @32
    gsumzsplit.g
    gsumzsplit.c
    @15
    cG
    @31
    @17
    cZ
    gsumzsplit.z
    @29
    @31
    eqid
    #
    cntzspan
    syl2anc
    wph
    @24
    @32
    @33
    wb
    @30
    @18
    cG
    @31
    cZ
    @34
    gsumzsplit.z
    submcmn2
    syl
    mpbid
    #
    wph
    vk
    cA
    @3
    @18
    @4
    wph
    @0
    cA
    wcel
    #
    wa
    #
    @1
    @2
    c.0
    @18
    @37
    @15
    @18
    @2
    wph
    @15
    @18
    wss
    @36
    wph
    @16
    @15
    @17
    cB
    @26
    @29
    @28
    mrcssidd
    adantr
    wph
    cF
    cA
    wfn
    #
    @36
    @2
    @15
    wcel
    wph
    @27
    @38
    gsumzsplit.f
    cA
    cB
    cF
    ffn
    syl
    cA
    @0
    cF
    fnfvelrn
    sylan
    sseldd
    #
    wph
    c.0
    @18
    wcel
    #
    @36
    wph
    @24
    @40
    @30
    @18
    cG
    c.0
    gsumzsplit.0
    subm0cl
    syl
    adantr
    #
    ifcld
    @4
    eqid
    #
    fmptd
    #
    wph
    vk
    cA
    @6
    @18
    @7
    @37
    @5
    @2
    c.0
    @18
    @39
    @41
    ifcld
    @7
    eqid
    #
    fmptd
    #
    gsumzadd
    wph
    cF
    @8
    cG
    cgsu
    wph
    cF
    vk
    cA
    @3
    @6
    c.pl
    co
    #
    cmpt
    #
    @8
    wph
    cF
    vk
    cA
    @2
    cmpt
    #
    @47
    wph
    vk
    cA
    cB
    cF
    gsumzsplit.f
    feqmptd
    #
    wph
    vk
    cA
    @46
    @2
    @37
    @1
    @46
    @2
    wceq
    @5
    @37
    @1
    wa
    #
    @46
    @2
    c.0
    c.pl
    co
    #
    @2
    @50
    @3
    @2
    @6
    c.0
    c.pl
    @1
    @3
    @2
    wceq
    @37
    @1
    @2
    c.0
    iftrue
    #
    adantl
    @50
    @5
    @2
    c.0
    @37
    @1
    @5
    wn
    #
    @37
    @1
    @5
    wa
    #
    wn
    @1
    @53
    wi
    @37
    @0
    cC
    cD
    cin
    #
    wcel
    #
    @54
    wph
    @56
    wn
    #
    @36
    wph
    @55
    c0
    wceq
    #
    @57
    gsumzsplit.i
    @58
    @56
    @0
    c0
    wcel
    @0
    noel
    @55
    c0
    @0
    eleq2
    mtbiri
    syl
    adantr
    @0
    cC
    cD
    elin
    sylnib
    @1
    @5
    imnan
    sylibr
    #
    imp
    iffalsed
    oveq12d
    @37
    @51
    @2
    wceq
    #
    @1
    wph
    @36
    @2
    cB
    wcel
    #
    @60
    wph
    cA
    cB
    @0
    cF
    gsumzsplit.f
    ffvelrnda
    #
    wph
    @25
    @61
    @60
    gsumzsplit.g
    cB
    c.pl
    cG
    @2
    c.0
    gsumzsplit.b
    gsumzsplit.p
    gsumzsplit.0
    mndrid
    sylan
    syldan
    adantr
    eqtrd
    @37
    @5
    wa
    #
    @46
    c.0
    @2
    c.pl
    co
    #
    @2
    @63
    @3
    c.0
    @6
    @2
    c.pl
    @63
    @1
    @2
    c.0
    @37
    @5
    @1
    wn
    #
    @37
    @1
    @5
    @59
    con2d
    imp
    iffalsed
    @5
    @6
    @2
    wceq
    @37
    @5
    @2
    c.0
    iftrue
    #
    adantl
    oveq12d
    @37
    @64
    @2
    wceq
    #
    @5
    wph
    @36
    @61
    @67
    @62
    wph
    @25
    @61
    @67
    gsumzsplit.g
    cB
    c.pl
    cG
    @2
    c.0
    gsumzsplit.b
    gsumzsplit.p
    gsumzsplit.0
    mndlid
    sylan
    syldan
    adantr
    eqtrd
    wph
    @36
    @1
    @5
    wo
    #
    wph
    @36
    @0
    cC
    cD
    cun
    #
    wcel
    @68
    wph
    cA
    @69
    @0
    gsumzsplit.u
    eleq2d
    @0
    cC
    cD
    elun
    syl6bb
    biimpa
    mpjaodan
    mpteq2dva
    eqtr4d
    wph
    vk
    cA
    @3
    @6
    c.pl
    @4
    @7
    cV
    cB
    cB
    gsumzsplit.a
    @37
    @1
    @2
    c.0
    cB
    @62
    wph
    c.0
    cB
    wcel
    #
    @36
    wph
    @25
    @70
    gsumzsplit.g
    cB
    cG
    c.0
    gsumzsplit.b
    gsumzsplit.0
    mndidcl
    syl
    adantr
    #
    ifcld
    #
    @37
    @5
    @2
    c.0
    cB
    @62
    @71
    ifcld
    #
    wph
    @4
    eqidd
    wph
    @7
    eqidd
    offval2
    eqtr4d
    oveq2d
    wph
    @12
    @9
    @14
    @10
    c.pl
    wph
    @12
    cG
    @4
    cC
    cres
    #
    cgsu
    co
    @9
    wph
    @11
    @74
    cG
    cgsu
    wph
    @11
    @48
    cC
    cres
    #
    @74
    wph
    cF
    @48
    cC
    @49
    reseq1d
    wph
    cC
    cA
    wss
    #
    @74
    @75
    wceq
    wph
    @69
    cC
    cA
    cC
    cD
    ssun1
    gsumzsplit.u
    syl5sseqr
    @76
    vk
    cC
    @3
    cmpt
    vk
    cC
    @2
    cmpt
    @74
    @75
    vk
    cC
    @3
    @2
    @52
    mpteq2ia
    vk
    cA
    cC
    @3
    resmpt
    vk
    cA
    cC
    @2
    resmpt
    3eqtr4a
    syl
    eqtr4d
    oveq2d
    wph
    cA
    cB
    @4
    cG
    cV
    cC
    c.0
    cZ
    gsumzsplit.b
    gsumzsplit.0
    gsumzsplit.z
    gsumzsplit.g
    gsumzsplit.a
    wph
    vk
    cA
    @3
    cB
    @4
    @72
    @42
    fmptd
    wph
    @33
    @4
    crn
    #
    @18
    wss
    #
    @77
    @77
    cZ
    cfv
    wss
    @35
    wph
    cA
    @18
    @4
    wf
    @78
    @43
    cA
    @18
    @4
    frn
    syl
    @18
    @77
    cG
    cZ
    gsumzsplit.z
    cntzidss
    syl2anc
    wph
    cA
    @3
    vk
    cV
    cC
    c.0
    wph
    @0
    cA
    cC
    cdif
    wcel
    #
    wa
    @1
    @2
    c.0
    @79
    @65
    wph
    @0
    cA
    cC
    eldifn
    adantl
    iffalsed
    gsumzsplit.a
    suppss2
    @20
    gsumzres
    eqtrd
    wph
    @14
    cG
    @7
    cD
    cres
    #
    cgsu
    co
    @10
    wph
    @13
    @80
    cG
    cgsu
    wph
    @13
    @48
    cD
    cres
    #
    @80
    wph
    cF
    @48
    cD
    @49
    reseq1d
    wph
    cD
    cA
    wss
    #
    @80
    @81
    wceq
    wph
    @69
    cD
    cA
    cD
    cC
    ssun2
    gsumzsplit.u
    syl5sseqr
    @82
    vk
    cD
    @6
    cmpt
    vk
    cD
    @2
    cmpt
    @80
    @81
    vk
    cD
    @6
    @2
    @66
    mpteq2ia
    vk
    cA
    cD
    @6
    resmpt
    vk
    cA
    cD
    @2
    resmpt
    3eqtr4a
    syl
    eqtr4d
    oveq2d
    wph
    cA
    cB
    @7
    cG
    cV
    cD
    c.0
    cZ
    gsumzsplit.b
    gsumzsplit.0
    gsumzsplit.z
    gsumzsplit.g
    gsumzsplit.a
    wph
    vk
    cA
    @6
    cB
    @7
    @73
    @44
    fmptd
    wph
    @33
    @7
    crn
    #
    @18
    wss
    #
    @83
    @83
    cZ
    cfv
    wss
    @35
    wph
    cA
    @18
    @7
    wf
    @84
    @45
    cA
    @18
    @7
    frn
    syl
    @18
    @83
    cG
    cZ
    gsumzsplit.z
    cntzidss
    syl2anc
    wph
    cA
    @6
    vk
    cV
    cD
    c.0
    wph
    @0
    cA
    cD
    cdif
    wcel
    #
    wa
    @5
    @2
    c.0
    @85
    @53
    wph
    @0
    cA
    cD
    eldifn
    adantl
    iffalsed
    gsumzsplit.a
    suppss2
    @21
    gsumzres
    eqtrd
    oveq12d
    3eqtr4d
end
