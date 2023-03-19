include "cv.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "chil.mm"
include "wral.mm"
include "wrex.mm"
include "cnl.mm"
include "cort.mm"
include "c0h.mm"
include "c0v.mm"
include "wcel.mm"
include "ax-hv0cl.mm"
include "wa.mm"
include "cc0.mm"
include "cc.mm"
include "wf.mm"
include "lnfnfi.mm"
include "fveq2.mm"
include "nlelchi.mm"
include "ococi.mm"
include "choc0.mm"
include "3eqtr3g.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "elnlfn2.mm"
include "sylancr.mm"
include "hi02.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "ralrimiva.mm"
include "oveq2.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "wne.mm"
include "choccli.mm"
include "chne0i.mm"
include "wi.mm"
include "cheli.mm"
include "cdiv.mm"
include "ccj.mm"
include "csm.mm"
include "ffvelrni.mm"
include "adantr.mm"
include "hicl.mm"
include "anidms.mm"
include "his6.mm"
include "necon3bid.mm"
include "divcld.mm"
include "cjcld.mm"
include "simpl.mm"
include "hvmulcl.mm"
include "syl2anc.mm"
include "adantll.mm"
include "cmul.mm"
include "cmin.mm"
include "cmv.mm"
include "sylan.mm"
include "ancoms.mm"
include "his2sub.mm"
include "syl3anc.mm"
include "simpr.mm"
include "ax-his3.mm"
include "oveq12d.mm"
include "eqtr2d.mm"
include "hvsubcl.mm"
include "lnfnsubi.mm"
include "lnfnmuli.mm"
include "mulcom.mm"
include "sylan2.mm"
include "eqtrd.mm"
include "mulcl.mm"
include "syl2an.mm"
include "subidd.mm"
include "3eqtrd.mm"
include "wb.mm"
include "elnlfn.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "wss.mm"
include "chssii.mm"
include "ocorth.mm"
include "anassrs.mm"
include "mulcld.mm"
include "syl2anr.mm"
include "subeq0ad.mm"
include "mpbid.mm"
include "adantlr.mm"
include "jca.mm"
include "divmul3.mm"
include "adantlll.mm"
include "mpbird.mm"
include "div23.mm"
include "simpll.mm"
include "his52.mm"
include "eqtr3d.mm"
include "ex.mm"
include "mpdan.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "pm2.61ine.mm"

theorem riesz3i
  let vw: setvar w
  let vv: setvar v
  let cT: class T
  let vf: setvar f
  let vn: setvar n
  let vu: setvar u
  let vx: setvar x
  assume nlelch.1: |- T e. LinFn
  assume nlelch.2: |- T e. ContFn

  disjoint v w
  disjoint T v
  disjoint T w
  disjoint f n
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint T f
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint T n
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint T u
  disjoint v x
  disjoint w x
  disjoint T x
  assert |- E. w e. ~H A. v e. ~H ( T ` v ) = ( v .ih w )

  proof
    vv
    cv
    #
    cT
    cfv
    #
    @0
    vw
    cv
    #
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    #
    vw
    chil
    wrex
    #
    cT
    cnl
    cfv
    #
    cort
    cfv
    #
    c0h
    @8
    c0h
    wceq
    #
    c0v
    chil
    wcel
    @1
    @0
    c0v
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    #
    @6
    ax-hv0cl
    @9
    @11
    vv
    chil
    @9
    @0
    chil
    wcel
    #
    wa
    #
    @1
    cc0
    @10
    @14
    chil
    cc
    cT
    wf
    #
    @0
    @7
    wcel
    #
    @1
    cc0
    wceq
    cT
    nlelch.1
    lnfnfi
    #
    @9
    @16
    @13
    @9
    @7
    chil
    @0
    @9
    @8
    cort
    cfv
    c0h
    cort
    cfv
    @7
    chil
    @8
    c0h
    cort
    fveq2
    @7
    cT
    nlelch.1
    nlelch.2
    nlelchi
    #
    ococi
    choc0
    3eqtr3g
    eleq2d
    biimpar
    @0
    cT
    elnlfn2
    sylancr
    @13
    @10
    cc0
    wceq
    @9
    @0
    hi02
    adantl
    eqtr4d
    ralrimiva
    @5
    @12
    vw
    c0v
    chil
    @2
    c0v
    wceq
    #
    @4
    @11
    vv
    chil
    @19
    @3
    @10
    @1
    @2
    c0v
    @0
    csp
    oveq2
    eqeq2d
    ralbidv
    rspcev
    sylancr
    @8
    c0h
    wne
    vu
    cv
    #
    c0v
    wne
    #
    vu
    @8
    wrex
    @6
    vu
    @8
    @7
    @18
    choccli
    #
    chne0i
    @21
    @6
    vu
    @8
    @20
    @8
    wcel
    #
    @20
    chil
    wcel
    #
    @21
    @6
    wi
    @20
    @8
    @22
    cheli
    @23
    @24
    wa
    #
    @21
    @6
    @25
    @21
    wa
    #
    @20
    cT
    cfv
    #
    @20
    @20
    csp
    co
    #
    cdiv
    co
    #
    ccj
    cfv
    #
    @20
    csm
    co
    #
    chil
    wcel
    #
    @1
    @0
    @31
    csp
    co
    #
    wceq
    #
    vv
    chil
    wral
    #
    @6
    @24
    @21
    @32
    @23
    @24
    @21
    wa
    #
    @30
    cc
    wcel
    @24
    @32
    @36
    @29
    @36
    @27
    @28
    @24
    @27
    cc
    wcel
    #
    @21
    chil
    cc
    @20
    cT
    @17
    ffvelrni
    #
    adantr
    #
    @24
    @28
    cc
    wcel
    #
    @21
    @24
    @40
    @20
    @20
    hicl
    anidms
    #
    adantr
    #
    @24
    @28
    cc0
    wne
    #
    @21
    @24
    @28
    cc0
    @20
    c0v
    @20
    his6
    necon3bid
    biimpar
    #
    divcld
    #
    cjcld
    @24
    @21
    simpl
    @30
    @20
    hvmulcl
    syl2anc
    adantll
    @26
    @34
    vv
    chil
    @26
    @13
    wa
    #
    @27
    @0
    @20
    csp
    co
    #
    cmul
    co
    #
    @28
    cdiv
    co
    #
    @1
    @33
    @46
    @49
    @1
    wceq
    #
    @48
    @1
    @28
    cmul
    co
    #
    wceq
    #
    @25
    @13
    @52
    @21
    @25
    @13
    wa
    #
    @48
    @51
    cmin
    co
    #
    cc0
    wceq
    #
    @52
    @53
    @54
    @27
    @0
    csm
    co
    #
    @1
    @20
    csm
    co
    #
    cmv
    co
    #
    @20
    csp
    co
    #
    cc0
    @24
    @13
    @54
    @59
    wceq
    @23
    @24
    @13
    wa
    #
    @59
    @56
    @20
    csp
    co
    #
    @57
    @20
    csp
    co
    #
    cmin
    co
    #
    @54
    @60
    @56
    chil
    wcel
    #
    @57
    chil
    wcel
    #
    @24
    @59
    @63
    wceq
    @24
    @37
    @13
    @64
    @38
    @27
    @0
    hvmulcl
    sylan
    #
    @13
    @24
    @65
    @13
    @1
    cc
    wcel
    #
    @24
    @65
    chil
    cc
    @0
    cT
    @17
    ffvelrni
    #
    @1
    @20
    hvmulcl
    sylan
    ancoms
    #
    @24
    @13
    simpl
    #
    @56
    @57
    @20
    his2sub
    syl3anc
    @60
    @61
    @48
    @62
    @51
    cmin
    @60
    @37
    @13
    @24
    @61
    @48
    wceq
    @24
    @37
    @13
    @38
    adantr
    #
    @24
    @13
    simpr
    @70
    @27
    @0
    @20
    ax-his3
    syl3anc
    @60
    @67
    @24
    @24
    @62
    @51
    wceq
    @13
    @67
    @24
    @68
    adantl
    @70
    @70
    @1
    @20
    @20
    ax-his3
    syl3anc
    oveq12d
    eqtr2d
    adantll
    @23
    @24
    @13
    @59
    cc0
    wceq
    #
    @60
    @23
    @72
    @60
    @58
    @7
    wcel
    #
    @23
    @72
    @60
    @58
    chil
    wcel
    #
    @58
    cT
    cfv
    #
    cc0
    wceq
    #
    @73
    @60
    @64
    @65
    @74
    @66
    @69
    @56
    @57
    hvsubcl
    syl2anc
    @60
    @75
    @56
    cT
    cfv
    #
    @57
    cT
    cfv
    #
    cmin
    co
    #
    @27
    @1
    cmul
    co
    #
    @80
    cmin
    co
    cc0
    @60
    @64
    @65
    @75
    @79
    wceq
    @66
    @69
    @56
    @57
    cT
    nlelch.1
    lnfnsubi
    syl2anc
    @60
    @77
    @80
    @78
    @80
    cmin
    @24
    @37
    @13
    @77
    @80
    wceq
    @38
    @27
    @0
    cT
    nlelch.1
    lnfnmuli
    sylan
    @13
    @24
    @78
    @80
    wceq
    #
    @13
    @67
    @24
    @81
    @68
    @67
    @24
    wa
    @78
    @1
    @27
    cmul
    co
    #
    @80
    @1
    @20
    cT
    nlelch.1
    lnfnmuli
    @24
    @67
    @37
    @82
    @80
    wceq
    @38
    @1
    @27
    mulcom
    sylan2
    eqtrd
    sylan
    ancoms
    oveq12d
    @60
    @80
    @24
    @37
    @67
    @80
    cc
    wcel
    @13
    @38
    @68
    @27
    @1
    mulcl
    syl2an
    subidd
    3eqtrd
    @15
    @73
    @74
    @76
    wa
    wb
    @17
    @58
    cT
    elnlfn
    ax-mp
    sylanbrc
    @7
    chil
    wss
    @73
    @23
    wa
    @72
    wi
    @7
    @18
    chssii
    @58
    @20
    @7
    ocorth
    ax-mp
    sylan
    ancoms
    anassrs
    eqtrd
    @24
    @13
    @55
    @52
    wb
    @23
    @60
    @48
    @51
    @60
    @27
    @47
    @71
    @13
    @24
    @47
    cc
    wcel
    #
    @0
    @20
    hicl
    ancoms
    #
    mulcld
    #
    @13
    @67
    @40
    @51
    cc
    wcel
    @24
    @68
    @41
    @1
    @28
    mulcl
    syl2anr
    subeq0ad
    adantll
    mpbid
    adantlr
    @24
    @21
    @13
    @50
    @52
    wb
    #
    @23
    @36
    @13
    wa
    #
    @48
    cc
    wcel
    #
    @67
    @40
    @43
    wa
    #
    @86
    @24
    @13
    @88
    @21
    @85
    adantlr
    @13
    @67
    @36
    @68
    adantl
    @36
    @89
    @13
    @36
    @40
    @43
    @42
    @44
    jca
    adantr
    #
    @48
    @1
    @28
    divmul3
    syl3anc
    adantlll
    mpbird
    @24
    @21
    @13
    @49
    @33
    wceq
    @23
    @87
    @49
    @29
    @47
    cmul
    co
    #
    @33
    @87
    @37
    @83
    @89
    @49
    @91
    wceq
    @36
    @37
    @13
    @39
    adantr
    @24
    @13
    @83
    @21
    @84
    adantlr
    @90
    @27
    @47
    @28
    div23
    syl3anc
    @87
    @29
    cc
    wcel
    #
    @13
    @24
    @33
    @91
    wceq
    @36
    @92
    @13
    @45
    adantr
    @36
    @13
    simpr
    @24
    @21
    @13
    simpll
    @29
    @0
    @20
    his52
    syl3anc
    eqtr4d
    adantlll
    eqtr3d
    ralrimiva
    @5
    @35
    vw
    @31
    chil
    @2
    @31
    wceq
    #
    @4
    @34
    vv
    chil
    @93
    @3
    @33
    @1
    @2
    @31
    @0
    csp
    oveq2
    eqeq2d
    ralbidv
    rspcev
    syl2anc
    ex
    mpdan
    rexlimiv
    sylbi
    pm2.61ine
end
