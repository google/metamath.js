include "crn.mm"
include "csn.mm"
include "cun.mm"
include "crest.mm"
include "co.mm"
include "ccmp.mm"
include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "wss.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "simprr.mm"
include "ssun2.mm"
include "wb.mm"
include "ctopon.mm"
include "cfv.mm"
include "clm.mm"
include "wbr.mm"
include "lmcl.mm"
include "syl2anc.mm"
include "snssg.mm"
include "syl.mm"
include "mpbiri.mm"
include "adantr.mm"
include "sseldd.mm"
include "eluni2.mm"
include "sylib.mm"
include "cuz.mm"
include "cn.mm"
include "c1.mm"
include "nnuz.mm"
include "1zzd.mm"
include "ad2antrr.mm"
include "simplrl.mm"
include "elpwid.mm"
include "simprl.mm"
include "lmcvg.mm"
include "cfz.mm"
include "cima.mm"
include "imassrn.mm"
include "ssun1.mm"
include "sstri.mm"
include "id.mm"
include "syl5ss.mm"
include "ctop.mm"
include "wf.mm"
include "frn.mm"
include "resttopon.mm"
include "topontop.mm"
include "cres.mm"
include "wfo.mm"
include "fzfid.mm"
include "wfun.mm"
include "cdm.mm"
include "ffun.mm"
include "elfznn.mm"
include "ssriv.mm"
include "wceq.mm"
include "fdm.mm"
include "syl5sseqr.mm"
include "fores.mm"
include "fofi.mm"
include "pwfi.mm"
include "restsspw.mm"
include "ssfi.mm"
include "sylancl.mm"
include "elind.mm"
include "fincmp.mm"
include "toponuni.mm"
include "sseqtrd.mm"
include "eqid.mm"
include "cmpsub.mm"
include "mpbid.mm"
include "r19.21bi.mm"
include "syl5.mm"
include "impr.mm"
include "inss1.mm"
include "sseldi.mm"
include "simprll.mm"
include "snssd.mm"
include "unssd.mm"
include "vex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "inss2.mm"
include "snfi.mm"
include "unfi.mm"
include "wfn.mm"
include "ffn.mm"
include "ad3antrrr.mm"
include "simprrr.mm"
include "fveq2.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "elun2.mm"
include "adantlr.mm"
include "elnnuz.mm"
include "anbi1i.mm"
include "elfzuzb.mm"
include "bitr4i.mm"
include "funimass4.mm"
include "elun1.mm"
include "sylan2b.mm"
include "anassrs.mm"
include "wo.mm"
include "ad2antlr.mm"
include "cz.mm"
include "nnz.mm"
include "uztric.mm"
include "syl2an.mm"
include "mpjaodan.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "uniun.mm"
include "unisn.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "syl6sseqr.mm"
include "unieq.mm"
include "sseq2d.mm"
include "rspcev.mm"
include "rexlimddv.mm"
include "expr.mm"
include "mpbird.mm"

theorem 1stckgenlem
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cJ: class J
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y
  assume 1stckgen.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume 1stckgen.2: |- ( ph -> F : NN --> X )
  assume 1stckgen.3: |- ( ph -> F ( ~~>t ` J ) A )


  assert |- ( ph -> ( J |`t ( ran F u. { A } ) ) e. Comp )

  proof
    wph
    cJ
    cF
    crn
    #
    cA
    csn
    #
    cun
    #
    crest
    co
    ccmp
    wcel
    #
    @2
    vu
    cv
    #
    cuni
    #
    wss
    #
    @2
    vv
    cv
    #
    cuni
    #
    wss
    #
    vv
    @4
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    wi
    #
    vu
    cJ
    cpw
    #
    wral
    #
    wph
    @13
    vu
    @14
    wph
    @4
    @14
    wcel
    #
    @6
    @12
    wph
    @16
    @6
    wa
    #
    wa
    #
    cA
    vw
    cv
    #
    wcel
    #
    @12
    vw
    @4
    @18
    cA
    @5
    wcel
    @20
    vw
    @4
    wrex
    @18
    @2
    @5
    cA
    wph
    @16
    @6
    simprr
    wph
    cA
    @2
    wcel
    #
    @17
    wph
    @21
    @1
    @2
    wss
    #
    @1
    @0
    ssun2
    wph
    cA
    cX
    wcel
    #
    @21
    @22
    wb
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cF
    cA
    cJ
    clm
    cfv
    wbr
    #
    @23
    1stckgen.1
    1stckgen.3
    cA
    cF
    cJ
    cX
    lmcl
    syl2anc
    #
    cA
    @2
    cX
    snssg
    syl
    mpbiri
    adantr
    sseldd
    vw
    cA
    @4
    eluni2
    sylib
    @18
    @19
    @4
    wcel
    #
    @20
    wa
    #
    wa
    #
    vk
    cv
    #
    cF
    cfv
    #
    @19
    wcel
    #
    vk
    vj
    cv
    #
    cuz
    cfv
    #
    wral
    #
    @12
    vj
    cn
    @29
    cA
    @19
    vj
    vk
    cF
    cJ
    c1
    cn
    nnuz
    @18
    @27
    @20
    simprr
    @29
    1zzd
    wph
    @25
    @17
    @28
    1stckgen.3
    ad2antrr
    @29
    @4
    cJ
    @19
    @29
    @4
    cJ
    wph
    @16
    @6
    @28
    simplrl
    elpwid
    @18
    @27
    @20
    simprl
    sseldd
    lmcvg
    @18
    @28
    @33
    cn
    wcel
    #
    @35
    wa
    #
    @12
    @18
    @28
    @37
    wa
    #
    wa
    #
    cF
    c1
    @33
    cfz
    co
    #
    cima
    #
    vs
    cv
    #
    cuni
    #
    wss
    #
    @12
    vs
    @11
    @18
    @44
    vs
    @11
    wrex
    #
    @38
    wph
    @16
    @6
    @45
    @6
    @41
    @5
    wss
    #
    wph
    @16
    wa
    @45
    @6
    @41
    @2
    @5
    @41
    @0
    @2
    cF
    @40
    imassrn
    #
    @0
    @1
    ssun1
    sstri
    @6
    id
    syl5ss
    wph
    @46
    @45
    wi
    #
    vu
    @14
    wph
    cJ
    @41
    crest
    co
    #
    ccmp
    wcel
    #
    @48
    vu
    @14
    wral
    #
    wph
    @49
    ctop
    cfn
    cin
    wcel
    @50
    wph
    ctop
    cfn
    @49
    wph
    @49
    @41
    ctopon
    cfv
    wcel
    #
    @49
    ctop
    wcel
    wph
    @24
    @41
    cX
    wss
    @52
    1stckgen.1
    wph
    @41
    @0
    cX
    @47
    wph
    cn
    cX
    cF
    wf
    #
    @0
    cX
    wss
    1stckgen.2
    cn
    cX
    cF
    frn
    syl
    #
    syl5ss
    #
    @41
    cJ
    cX
    resttopon
    syl2anc
    @41
    @49
    topontop
    syl
    wph
    @41
    cpw
    #
    cfn
    wcel
    #
    @49
    @56
    wss
    @49
    cfn
    wcel
    wph
    @41
    cfn
    wcel
    #
    @57
    wph
    @40
    cfn
    wcel
    @40
    @41
    cF
    @40
    cres
    #
    wfo
    #
    @58
    wph
    c1
    @33
    fzfid
    wph
    cF
    wfun
    #
    @40
    cF
    cdm
    #
    wss
    #
    @60
    wph
    @53
    @61
    1stckgen.2
    cn
    cX
    cF
    ffun
    syl
    #
    wph
    cn
    @40
    @62
    vn
    @40
    cn
    vn
    cv
    #
    @33
    elfznn
    ssriv
    wph
    @53
    @62
    cn
    wceq
    1stckgen.2
    cn
    cX
    cF
    fdm
    syl
    syl5sseqr
    #
    @40
    cF
    fores
    syl2anc
    @40
    @41
    @59
    fofi
    syl2anc
    @41
    pwfi
    sylib
    @41
    cJ
    restsspw
    @56
    @49
    ssfi
    sylancl
    elind
    @49
    fincmp
    syl
    wph
    cJ
    ctop
    wcel
    #
    @41
    cJ
    cuni
    #
    wss
    @50
    @51
    wb
    wph
    @24
    @67
    1stckgen.1
    cX
    cJ
    topontop
    syl
    #
    wph
    @41
    cX
    @68
    @55
    wph
    @24
    cX
    @68
    wceq
    1stckgen.1
    cX
    cJ
    toponuni
    syl
    #
    sseqtrd
    @41
    cJ
    @68
    vu
    vs
    @68
    eqid
    #
    cmpsub
    syl2anc
    mpbid
    r19.21bi
    syl5
    impr
    adantr
    @39
    @42
    @11
    wcel
    #
    @44
    wa
    #
    wa
    #
    @42
    @19
    csn
    #
    cun
    #
    @11
    wcel
    @2
    @76
    cuni
    #
    wss
    #
    @12
    @74
    @10
    cfn
    @76
    @74
    @76
    @4
    wss
    @76
    @10
    wcel
    @74
    @42
    @75
    @4
    @74
    @42
    @4
    @74
    @11
    @10
    @42
    @10
    cfn
    inss1
    @39
    @72
    @44
    simprl
    #
    sseldi
    elpwid
    @74
    @19
    @4
    @39
    @27
    @73
    @18
    @27
    @20
    @37
    simprll
    adantr
    snssd
    unssd
    @76
    @4
    vu
    vex
    elpw2
    sylibr
    @74
    @42
    cfn
    wcel
    @75
    cfn
    wcel
    @76
    cfn
    wcel
    @74
    @11
    cfn
    @42
    @10
    cfn
    inss2
    @79
    sseldi
    @19
    snfi
    @42
    @75
    unfi
    sylancl
    elind
    @74
    @2
    @43
    @19
    cun
    #
    @77
    @74
    @0
    @1
    @80
    @74
    cF
    cn
    wfn
    #
    @65
    cF
    cfv
    #
    @80
    wcel
    #
    vn
    cn
    wral
    @0
    @80
    wss
    wph
    @81
    @17
    @38
    @73
    wph
    @53
    @81
    1stckgen.2
    cn
    cX
    cF
    ffn
    syl
    ad3antrrr
    @74
    @83
    vn
    cn
    @74
    @65
    cn
    wcel
    #
    wa
    @65
    @34
    wcel
    #
    @83
    @33
    @65
    cuz
    cfv
    wcel
    #
    @74
    @85
    @83
    @84
    @74
    @85
    wa
    @82
    @19
    wcel
    #
    @83
    @74
    @35
    @85
    @87
    @39
    @35
    @73
    @18
    @28
    @36
    @35
    simprrr
    adantr
    @32
    @87
    vk
    @65
    @34
    @30
    @65
    wceq
    @31
    @82
    @19
    @30
    @65
    cF
    fveq2
    eleq1d
    rspccva
    sylan
    @82
    @19
    @43
    elun2
    syl
    adantlr
    @74
    @84
    @86
    @83
    @84
    @86
    wa
    #
    @74
    @65
    @40
    wcel
    #
    @83
    @88
    @65
    c1
    cuz
    cfv
    wcel
    #
    @86
    wa
    @89
    @84
    @90
    @86
    @65
    elnnuz
    anbi1i
    @65
    c1
    @33
    elfzuzb
    bitr4i
    @74
    @89
    wa
    @82
    @43
    wcel
    #
    @83
    @74
    @91
    vn
    @40
    @74
    @44
    @91
    vn
    @40
    wral
    #
    @39
    @72
    @44
    simprr
    wph
    @44
    @92
    wb
    #
    @17
    @38
    @73
    wph
    @61
    @63
    @93
    @64
    @66
    vn
    @40
    @43
    cF
    funimass4
    syl2anc
    ad3antrrr
    mpbid
    r19.21bi
    @82
    @43
    @19
    elun1
    syl
    sylan2b
    anassrs
    @74
    @36
    @84
    @85
    @86
    wo
    #
    @38
    @36
    @18
    @73
    @28
    @36
    @35
    simprl
    ad2antlr
    @36
    @33
    cz
    wcel
    @65
    cz
    wcel
    @94
    @84
    @33
    nnz
    @65
    nnz
    @33
    @65
    uztric
    syl2an
    sylan
    mpjaodan
    ralrimiva
    vn
    cn
    @80
    cF
    fnfvrnss
    syl2anc
    @74
    cA
    @80
    @38
    cA
    @80
    wcel
    #
    @18
    @73
    @20
    @95
    @27
    @37
    cA
    @19
    @43
    elun2
    ad2antlr
    ad2antlr
    snssd
    unssd
    @77
    @43
    @75
    cuni
    #
    cun
    @80
    @42
    @75
    uniun
    @96
    @19
    @43
    @19
    vw
    vex
    unisn
    uneq2i
    eqtri
    syl6sseqr
    @9
    @78
    vv
    @76
    @11
    @7
    @76
    wceq
    @8
    @77
    @2
    @7
    @76
    unieq
    sseq2d
    rspcev
    syl2anc
    rexlimddv
    anassrs
    rexlimddv
    rexlimddv
    expr
    ralrimiva
    wph
    @67
    @2
    @68
    wss
    @3
    @15
    wb
    @69
    wph
    @2
    cX
    @68
    wph
    @0
    @1
    cX
    @54
    wph
    cA
    cX
    @26
    snssd
    unssd
    @70
    sseqtrd
    @2
    cJ
    @68
    vu
    vv
    @71
    cmpsub
    syl2anc
    mpbird
end
