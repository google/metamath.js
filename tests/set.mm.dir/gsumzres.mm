include "csupp.mm"
include "co.mm"
include "c0.mm"
include "wceq.mm"
include "cres.mm"
include "cgsu.mm"
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
include "cin.mm"
include "cmpt.mm"
include "cmnd.mm"
include "cvv.mm"
include "inex1g.mm"
include "syl.mm"
include "gsumz.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "adantr.mm"
include "resres.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "fnresdm.mm"
include "3syl.mm"
include "reseq1d.mm"
include "syl5eqr.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "wss.mm"
include "ssid.mm"
include "gsumcllem.mm"
include "inss1.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "eqtr3d.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "cplusg.mm"
include "ccom.mm"
include "cseq.mm"
include "crn.mm"
include "wfo.mm"
include "f1ofo.mm"
include "forn.mm"
include "ad2antll.mm"
include "eqsstrd.mm"
include "cores.mm"
include "seqeq3d.mm"
include "fveq1d.mm"
include "eqid.mm"
include "fssres.mm"
include "sylancl.mm"
include "feq1d.mm"
include "biimpa.mm"
include "syldan.mm"
include "resss.mm"
include "rnss.mm"
include "cntzidss.mm"
include "simprl.mm"
include "wf1.mm"
include "f1of1.mm"
include "cdm.mm"
include "suppssdm.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "ssind.mm"
include "f1ss.mm"
include "wi.mm"
include "fex.mm"
include "ressuppss.mm"
include "sseq2.mm"
include "syl5ibr.mm"
include "adantl.mm"
include "impcom.mm"
include "gsumval3.mm"
include "syl5sseqr.mm"
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

theorem gsumzres
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let cZ: class Z
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let cH: class H
  let cC: class C
  assume gsumzcl.b: |- B = ( Base ` G )
  assume gsumzcl.0: |- .0. = ( 0g ` G )
  assume gsumzcl.z: |- Z = ( Cntz ` G )
  assume gsumzcl.g: |- ( ph -> G e. Mnd )
  assume gsumzcl.a: |- ( ph -> A e. V )
  assume gsumzcl.f: |- ( ph -> F : A --> B )
  assume gsumzcl.c: |- ( ph -> ran F C_ ( Z ` ran F ) )
  assume gsumzres.s: |- ( ph -> ( F supp .0. ) C_ W )
  assume gsumzres.w: |- ( ph -> F finSupp .0. )


  assert |- ( ph -> ( G gsum ( F |` W ) ) = ( G gsum F ) )

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
    cW
    cres
    #
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
    cW
    cin
    #
    c.0
    cmpt
    #
    cgsu
    co
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
    @3
    @4
    wph
    @16
    @18
    wceq
    @1
    wph
    @16
    c.0
    @18
    wph
    cG
    cmnd
    wcel
    #
    @14
    cvv
    wcel
    #
    @16
    c.0
    wceq
    gsumzcl.g
    wph
    cA
    cV
    wcel
    #
    @20
    gsumzcl.a
    cA
    cW
    cV
    inex1g
    syl
    #
    @14
    vk
    cG
    cvv
    c.0
    gsumzcl.0
    gsumz
    syl2anc
    wph
    @19
    @21
    @18
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
    eqtr4d
    adantr
    @13
    @2
    @15
    cG
    cgsu
    @13
    cF
    @14
    cres
    #
    @2
    @15
    wph
    @23
    @2
    wceq
    @1
    wph
    @23
    cF
    cA
    cres
    #
    cW
    cres
    @2
    cF
    cA
    cW
    resres
    wph
    @24
    cF
    cW
    wph
    cA
    cB
    cF
    wf
    #
    cF
    cA
    wfn
    @24
    cF
    wceq
    gsumzcl.f
    cA
    cB
    cF
    ffn
    cA
    cF
    fnresdm
    3syl
    reseq1d
    syl5eqr
    #
    adantr
    @13
    @23
    @17
    @14
    cres
    #
    @15
    @13
    cF
    @17
    @14
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
    wph
    @0
    ssid
    #
    a1i
    gsumcllem
    #
    reseq1d
    @14
    cA
    wss
    #
    @27
    @15
    wceq
    cA
    cW
    inss1
    #
    vk
    cA
    @14
    c.0
    resmpt
    ax-mp
    syl6eq
    eqtr3d
    oveq2d
    @13
    cF
    @17
    cG
    cgsu
    @31
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
    @2
    @9
    ccom
    #
    c1
    cseq
    #
    cfv
    @6
    @36
    cF
    @9
    ccom
    #
    c1
    cseq
    #
    cfv
    @3
    @4
    @35
    @6
    @38
    @40
    @35
    @37
    @39
    @36
    c1
    @35
    @9
    crn
    #
    cW
    wss
    @37
    @39
    wceq
    @35
    @41
    @0
    cW
    @10
    @41
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
    #
    @42
    @8
    @0
    @9
    f1ofo
    #
    @8
    @0
    @9
    forn
    #
    syl
    ad2antll
    #
    wph
    @0
    cW
    wss
    @34
    gsumzres.s
    adantr
    eqsstrd
    cF
    @9
    cW
    cores
    syl
    seqeq3d
    fveq1d
    @35
    @14
    cB
    @36
    @2
    cG
    @9
    @6
    cvv
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
    @19
    @34
    gsumzcl.g
    adantr
    #
    wph
    @20
    @34
    @22
    adantr
    wph
    @34
    @14
    cB
    @23
    wf
    #
    @14
    cB
    @2
    wf
    #
    @35
    @25
    @32
    @50
    wph
    @25
    @34
    gsumzcl.f
    adantr
    #
    @33
    cA
    cB
    @14
    cF
    fssres
    sylancl
    wph
    @50
    @51
    wph
    @14
    cB
    @23
    @2
    @26
    feq1d
    biimpa
    syldan
    wph
    @2
    crn
    #
    @53
    cZ
    cfv
    wss
    #
    @34
    wph
    cF
    crn
    #
    @55
    cZ
    cfv
    wss
    #
    @53
    @55
    wss
    #
    @54
    gsumzcl.c
    @2
    cF
    wss
    @57
    cF
    cW
    resss
    @2
    cF
    rnss
    ax-mp
    @55
    @53
    cG
    cZ
    gsumzcl.z
    cntzidss
    sylancl
    adantr
    wph
    @7
    @10
    simprl
    #
    @35
    @8
    @0
    @9
    wf1
    #
    @0
    @14
    wss
    #
    @8
    @14
    @9
    wf1
    @10
    @59
    wph
    @7
    @8
    @0
    @9
    f1of1
    ad2antll
    #
    wph
    @60
    @34
    wph
    @0
    cA
    cW
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
    @25
    @62
    cA
    wceq
    gsumzcl.f
    cA
    cB
    cF
    fdm
    syl
    syl5sseq
    #
    gsumzres.s
    ssind
    adantr
    @8
    @0
    @14
    @9
    f1ss
    syl2anc
    @34
    wph
    @2
    c.0
    csupp
    co
    #
    @41
    wss
    #
    @10
    wph
    @65
    wi
    #
    @7
    @10
    @43
    @42
    @66
    @44
    @45
    wph
    @65
    @42
    @64
    @0
    wss
    #
    wph
    cF
    cvv
    wcel
    #
    @28
    @67
    wph
    @25
    @21
    @68
    gsumzcl.f
    gsumzcl.a
    cA
    cB
    cV
    cF
    fex
    syl2anc
    @29
    cW
    cF
    cvv
    cvv
    c.0
    ressuppss
    sylancl
    @41
    @0
    @64
    sseq2
    syl5ibr
    3syl
    adantl
    impcom
    @47
    eqid
    gsumval3
    @35
    cA
    cB
    @36
    cF
    cG
    @9
    @6
    cV
    @39
    c.0
    csupp
    co
    #
    c.0
    cZ
    gsumzcl.b
    gsumzcl.0
    @48
    gsumzcl.z
    @49
    wph
    @21
    @34
    gsumzcl.a
    adantr
    @52
    wph
    @56
    @34
    gsumzcl.c
    adantr
    @58
    @35
    @59
    @0
    cA
    wss
    #
    @8
    cA
    @9
    wf1
    @61
    wph
    @70
    @34
    @63
    adantr
    @8
    @0
    cA
    @9
    f1ss
    syl2anc
    @35
    @0
    @0
    @41
    @30
    @46
    syl5sseqr
    @69
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
    gsumzres.w
    @71
    cF
    wfun
    @72
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
