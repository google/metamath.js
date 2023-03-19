include "c1.mm"
include "chash.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "csn.mm"
include "cxp.mm"
include "ccxp.mm"
include "cof.mm"
include "cgsu.mm"
include "ccnfld.mm"
include "cmul.mm"
include "cle.mm"
include "crp.mm"
include "wcel.mm"
include "wf.mm"
include "cn.mm"
include "c0.mm"
include "wne.mm"
include "cfn.mm"
include "wb.mm"
include "hashnncl.mm"
include "syl.mm"
include "mpbird.mm"
include "nnrpd.mm"
include "rpreccld.mm"
include "fconst6g.mm"
include "cmpt.mm"
include "csu.mm"
include "wceq.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "oveq2d.mm"
include "cc.mm"
include "nnrecred.mm"
include "recnd.mm"
include "wa.mm"
include "simpl.mm"
include "cv.mm"
include "simplr.mm"
include "gsumfsum.mm"
include "syl2anc.mm"
include "fsumconst.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "recidd.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "amgmwlem.mm"
include "cress.mm"
include "ccom.mm"
include "wss.mm"
include "cbs.mm"
include "cr.mm"
include "rpssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "eqid.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "c0g.mm"
include "cnfld1.mm"
include "ringidval.mm"
include "csubmnd.mm"
include "cc0.mm"
include "cdif.mm"
include "csubg.mm"
include "cmgp.mm"
include "oveq1i.mm"
include "rpmsubg.mm"
include "subgsubm.mm"
include "crg.mm"
include "cnring.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "unitsubm.mm"
include "subsubm.mm"
include "mpbi.mm"
include "simpli.mm"
include "subm0.mm"
include "eqtri.mm"
include "ccmn.mm"
include "cmnd.mm"
include "ccrg.mm"
include "cncrng.mm"
include "crngmgp.mm"
include "submmnd.mm"
include "mp1i.mm"
include "subcmn.mm"
include "sylancr.mm"
include "cghm.mm"
include "cmhm.mm"
include "cvv.mm"
include "cplusg.mm"
include "reex.mm"
include "ssexi.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "ressplusg.mm"
include "cgrp.mm"
include "cnex.mm"
include "difss.mm"
include "rpcndif0.mm"
include "ssriv.mm"
include "ressabs.mm"
include "mp2an.mm"
include "eqtr4i.mm"
include "subggrp.mm"
include "simpr.mm"
include "adantr.mm"
include "rpcxpcld.mm"
include "fmptd.mm"
include "wbr.mm"
include "simprl.mm"
include "rprege0d.mm"
include "simprr.mm"
include "mulcxp.mm"
include "syl3anc.mm"
include "rpmulcl.mm"
include "adantl.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt3i.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"
include "isghmd.mm"
include "ghmmhm.mm"
include "1red.mm"
include "fdmfifsupp.mm"
include "gsummhm.mm"
include "ffvelrnda.mm"
include "gsumsubm.mm"
include "feqmptd.mm"
include "offval2.mm"
include "cbvmptv.mm"
include "fmptco.mm"
include "3eqtr4rd.mm"
include "gsumcl.mm"
include "oveq1d.mm"
include "eqtr4d.mm"
include "3eqtr3d.mm"
include "rpcnd.mm"
include "fsumcl.mm"
include "divrecd.mm"
include "fsummulc1.mm"
include "eqtr2d.mm"
include "mulcld.mm"
include "3brtr3d.mm"

theorem amgmlemALT
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  assume amgmlemALT.0: |- M = ( mulGrp ` CCfld )
  assume amgmlemALT.1: |- ( ph -> A e. Fin )
  assume amgmlemALT.2: |- ( ph -> A =/= (/) )
  assume amgmlemALT.3: |- ( ph -> F : A --> RR+ )


  assert |- ( ph -> ( ( M gsum F ) ^c ( 1 / ( # ` A ) ) ) <_ ( ( CCfld gsum F ) / ( # ` A ) ) )

  proof
    wph
    cM
    cF
    cA
    c1
    cA
    chash
    cfv
    #
    cdiv
    co
    #
    csn
    cxp
    #
    ccxp
    cof
    co
    #
    cgsu
    co
    #
    ccnfld
    cF
    @2
    cmul
    cof
    co
    #
    cgsu
    co
    #
    cM
    cF
    cgsu
    co
    #
    @1
    ccxp
    co
    #
    ccnfld
    cF
    cgsu
    co
    #
    @0
    cdiv
    co
    #
    cle
    wph
    cA
    cF
    cM
    @2
    amgmlemALT.0
    amgmlemALT.1
    amgmlemALT.2
    amgmlemALT.3
    wph
    @1
    crp
    wcel
    #
    cA
    crp
    @2
    wf
    wph
    @0
    wph
    @0
    wph
    @0
    cn
    wcel
    #
    cA
    c0
    wne
    #
    amgmlemALT.2
    wph
    cA
    cfn
    wcel
    #
    @12
    @13
    wb
    amgmlemALT.1
    cA
    hashnncl
    syl
    mpbird
    #
    nnrpd
    rpreccld
    #
    cA
    @1
    crp
    fconst6g
    syl
    wph
    ccnfld
    @2
    cgsu
    co
    ccnfld
    vk
    cA
    @1
    cmpt
    #
    cgsu
    co
    #
    cA
    @1
    vk
    csu
    #
    c1
    wph
    @2
    @17
    ccnfld
    cgsu
    @2
    @17
    wceq
    wph
    vk
    cA
    @1
    fconstmpt
    a1i
    #
    oveq2d
    wph
    @14
    @1
    cc
    wcel
    #
    @18
    @19
    wceq
    amgmlemALT.1
    wph
    @1
    wph
    @0
    @15
    nnrecred
    #
    recnd
    #
    @14
    @21
    wa
    cA
    @1
    vk
    @14
    @21
    simpl
    @14
    @21
    vk
    cv
    #
    cA
    wcel
    #
    simplr
    gsumfsum
    syl2anc
    wph
    @19
    @0
    @1
    cmul
    co
    #
    c1
    wph
    @14
    @21
    @19
    @26
    wceq
    amgmlemALT.1
    @23
    cA
    @1
    vk
    fsumconst
    syl2anc
    wph
    @0
    wph
    @0
    @15
    nncnd
    #
    wph
    @0
    @15
    nnne0d
    #
    recidd
    eqtrd
    3eqtrd
    amgmwlem
    wph
    cM
    crp
    cress
    co
    #
    vk
    crp
    @24
    @1
    ccxp
    co
    #
    cmpt
    #
    cF
    ccom
    #
    cgsu
    co
    #
    @29
    cF
    cgsu
    co
    #
    @31
    cfv
    #
    @4
    @8
    wph
    cA
    crp
    cF
    @29
    @29
    @31
    cfn
    c1
    crp
    cc
    wss
    crp
    @29
    cbs
    cfv
    wceq
    crp
    cr
    cc
    rpssre
    ax-resscn
    sstri
    crp
    cc
    @29
    cM
    @29
    eqid
    #
    cc
    ccnfld
    cM
    amgmlemALT.0
    cnfldbas
    mgpbas
    ressbas2
    ax-mp
    #
    c1
    cM
    c0g
    cfv
    #
    @29
    c0g
    cfv
    #
    ccnfld
    c1
    cM
    amgmlemALT.0
    cnfld1
    ringidval
    crp
    cM
    csubmnd
    cfv
    #
    wcel
    #
    @38
    @39
    wceq
    @41
    crp
    cc
    cc0
    csn
    #
    cdif
    #
    wss
    #
    crp
    cM
    @43
    cress
    co
    #
    csubmnd
    cfv
    wcel
    #
    @41
    @44
    wa
    #
    crp
    @45
    csubg
    cfv
    wcel
    @46
    @45
    cM
    ccnfld
    cmgp
    cfv
    #
    @43
    cress
    amgmlemALT.0
    oveq1i
    rpmsubg
    crp
    @45
    subgsubm
    ax-mp
    @43
    @40
    wcel
    #
    @46
    @47
    wb
    ccnfld
    crg
    wcel
    @49
    cnring
    ccnfld
    @43
    cM
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    amgmlemALT.0
    unitsubm
    ax-mp
    crp
    @43
    cM
    @45
    @45
    eqid
    subsubm
    ax-mp
    mpbi
    simpli
    #
    crp
    @29
    cM
    @38
    @36
    @38
    eqid
    subm0
    ax-mp
    eqtri
    #
    wph
    cM
    ccmn
    wcel
    #
    @29
    cmnd
    wcel
    #
    @29
    ccmn
    wcel
    ccnfld
    ccrg
    wcel
    @52
    cncrng
    ccnfld
    cM
    amgmlemALT.0
    crngmgp
    ax-mp
    @41
    @53
    wph
    @50
    crp
    @29
    cM
    @36
    submmnd
    mp1i
    #
    crp
    cM
    @29
    @36
    subcmn
    sylancr
    #
    @54
    amgmlemALT.1
    wph
    @31
    @29
    @29
    cghm
    co
    wcel
    @31
    @29
    @29
    cmhm
    co
    wcel
    wph
    vx
    vy
    cmul
    cmul
    @29
    @29
    @31
    crp
    crp
    @37
    @37
    crp
    cvv
    wcel
    cmul
    @29
    cplusg
    cfv
    wceq
    crp
    cr
    reex
    rpssre
    ssexi
    crp
    cmul
    cM
    @29
    cvv
    @36
    ccnfld
    cmul
    cM
    amgmlemALT.0
    cnfldmul
    mgpplusg
    ressplusg
    ax-mp
    #
    @56
    crp
    @48
    @43
    cress
    co
    #
    csubg
    cfv
    wcel
    @29
    cgrp
    wcel
    wph
    @57
    @57
    eqid
    rpmsubg
    crp
    @57
    @29
    @29
    @48
    crp
    cress
    co
    #
    @57
    crp
    cress
    co
    #
    cM
    @48
    crp
    cress
    amgmlemALT.0
    oveq1i
    @43
    cvv
    wcel
    @44
    @59
    @58
    wceq
    @43
    cc
    cnex
    cc
    @42
    difss
    ssexi
    vw
    crp
    @43
    vw
    cv
    rpcndif0
    ssriv
    @43
    crp
    @48
    cvv
    ressabs
    mp2an
    eqtr4i
    subggrp
    mp1i
    #
    @60
    wph
    vk
    crp
    @30
    crp
    @31
    wph
    @24
    crp
    wcel
    #
    wa
    @24
    @1
    wph
    @61
    simpr
    wph
    @1
    cr
    wcel
    #
    @61
    @22
    adantr
    rpcxpcld
    @31
    eqid
    #
    fmptd
    wph
    vx
    cv
    #
    crp
    wcel
    #
    vy
    cv
    #
    crp
    wcel
    #
    wa
    #
    wa
    #
    @64
    @66
    cmul
    co
    #
    @1
    ccxp
    co
    #
    @64
    @1
    ccxp
    co
    #
    @66
    @1
    ccxp
    co
    #
    cmul
    co
    #
    @70
    @31
    cfv
    #
    @64
    @31
    cfv
    #
    @66
    @31
    cfv
    #
    cmul
    co
    @69
    @64
    cr
    wcel
    cc0
    @64
    cle
    wbr
    wa
    @66
    cr
    wcel
    cc0
    @66
    cle
    wbr
    wa
    @21
    @71
    @74
    wceq
    @69
    @64
    wph
    @65
    @67
    simprl
    #
    rprege0d
    @69
    @66
    wph
    @65
    @67
    simprr
    #
    rprege0d
    wph
    @21
    @68
    @23
    adantr
    @64
    @66
    @1
    mulcxp
    syl3anc
    @69
    @70
    crp
    wcel
    #
    @75
    @71
    wceq
    @68
    @80
    wph
    @64
    @66
    rpmulcl
    adantl
    vk
    @70
    @30
    @71
    crp
    @31
    @24
    @70
    @1
    ccxp
    oveq1
    @63
    @24
    @1
    ccxp
    ovex
    #
    fvmpt3i
    syl
    @69
    @76
    @72
    @77
    @73
    cmul
    @69
    @65
    @76
    @72
    wceq
    @78
    vk
    @64
    @30
    @72
    crp
    @31
    @24
    @64
    @1
    ccxp
    oveq1
    #
    @63
    @81
    fvmpt3i
    syl
    @69
    @67
    @77
    @73
    wceq
    @79
    vk
    @66
    @30
    @73
    crp
    @31
    @24
    @66
    @1
    ccxp
    oveq1
    @63
    @81
    fvmpt3i
    syl
    oveq12d
    3eqtr4d
    isghmd
    @29
    @29
    @31
    ghmmhm
    syl
    amgmlemALT.3
    wph
    cA
    crp
    cF
    cr
    c1
    amgmlemALT.3
    amgmlemALT.1
    wph
    1red
    fdmfifsupp
    #
    gsummhm
    wph
    cM
    vk
    cA
    @24
    cF
    cfv
    #
    @1
    ccxp
    co
    #
    cmpt
    #
    cgsu
    co
    @29
    @86
    cgsu
    co
    @4
    @33
    wph
    cA
    crp
    @86
    cM
    @29
    cfn
    amgmlemALT.1
    @41
    wph
    @50
    a1i
    #
    wph
    vk
    cA
    @85
    crp
    @86
    wph
    @25
    wa
    #
    @84
    @1
    wph
    cA
    crp
    @24
    cF
    amgmlemALT.3
    ffvelrnda
    #
    wph
    @62
    @25
    @22
    adantr
    rpcxpcld
    @86
    eqid
    fmptd
    @36
    gsumsubm
    wph
    @3
    @86
    cM
    cgsu
    wph
    vk
    cA
    @84
    @1
    ccxp
    cF
    @2
    cfn
    crp
    crp
    amgmlemALT.1
    @89
    wph
    @11
    @25
    @16
    adantr
    wph
    vk
    cA
    crp
    cF
    amgmlemALT.3
    feqmptd
    #
    @20
    offval2
    oveq2d
    wph
    @32
    @86
    @29
    cgsu
    wph
    vk
    vx
    cA
    crp
    @84
    @72
    @85
    cF
    @31
    @89
    @90
    @31
    vx
    crp
    @72
    cmpt
    wceq
    wph
    vk
    vx
    crp
    @30
    @72
    @82
    cbvmptv
    a1i
    @64
    @84
    @1
    ccxp
    oveq1
    fmptco
    oveq2d
    3eqtr4rd
    wph
    @35
    @34
    @1
    ccxp
    co
    #
    @8
    wph
    @34
    crp
    wcel
    @35
    @91
    wceq
    wph
    cA
    crp
    cF
    @29
    cfn
    c1
    @37
    @51
    @55
    amgmlemALT.1
    amgmlemALT.3
    @83
    gsumcl
    vk
    @34
    @30
    @91
    crp
    @31
    @24
    @34
    @1
    ccxp
    oveq1
    @63
    @81
    fvmpt3i
    syl
    wph
    @7
    @34
    @1
    ccxp
    wph
    cA
    crp
    cF
    cM
    @29
    cfn
    amgmlemALT.1
    @87
    amgmlemALT.3
    @36
    gsumsubm
    oveq1d
    eqtr4d
    3eqtr3d
    wph
    ccnfld
    vk
    cA
    @84
    @1
    cmul
    co
    #
    cmpt
    #
    cgsu
    co
    #
    ccnfld
    vk
    cA
    @84
    cmpt
    #
    cgsu
    co
    #
    @0
    cdiv
    co
    #
    @6
    @10
    wph
    cA
    @92
    vk
    csu
    #
    cA
    @84
    vk
    csu
    #
    @0
    cdiv
    co
    #
    @94
    @97
    wph
    @100
    @99
    @1
    cmul
    co
    @98
    wph
    @99
    @0
    wph
    cA
    @84
    vk
    amgmlemALT.1
    @88
    @84
    @89
    rpcnd
    #
    fsumcl
    @27
    @28
    divrecd
    wph
    cA
    @84
    @1
    vk
    amgmlemALT.1
    @23
    @101
    fsummulc1
    eqtr2d
    wph
    cA
    @92
    vk
    amgmlemALT.1
    @88
    @84
    @1
    @101
    wph
    @21
    @25
    @23
    adantr
    #
    mulcld
    gsumfsum
    wph
    @96
    @99
    @0
    cdiv
    wph
    cA
    @84
    vk
    amgmlemALT.1
    @101
    gsumfsum
    oveq1d
    3eqtr4d
    wph
    @5
    @93
    ccnfld
    cgsu
    wph
    vk
    cA
    @84
    @1
    cmul
    cF
    @2
    cfn
    crp
    cc
    amgmlemALT.1
    @89
    @102
    @90
    @20
    offval2
    oveq2d
    wph
    @9
    @96
    @0
    cdiv
    wph
    cF
    @95
    ccnfld
    cgsu
    @90
    oveq2d
    oveq1d
    3eqtr4d
    3brtr3d
end
