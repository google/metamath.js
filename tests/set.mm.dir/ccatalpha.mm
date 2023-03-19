include "cvv.mm"
include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "chash.mm"
include "cfv.mm"
include "caddc.mm"
include "cfzo.mm"
include "cv.mm"
include "cmin.mm"
include "cif.mm"
include "cmpt.mm"
include "ccatfval.mm"
include "eleq1d.mm"
include "wf.mm"
include "wrdf.mm"
include "cdm.mm"
include "wfun.mm"
include "wceq.mm"
include "funmpt.mm"
include "cfn.mm"
include "wb.mm"
include "fzofi.mm"
include "mptfi.mm"
include "ax-mp.mm"
include "hashfun.mm"
include "mp1i.mm"
include "mpbii.mm"
include "dmmptg.mm"
include "fvex.mm"
include "ifex.mm"
include "a1i.mm"
include "mprg.mm"
include "fveq2i.mm"
include "cn0.mm"
include "lencl.mm"
include "nn0addcl.mm"
include "syl2an.mm"
include "hashfzo0.mm"
include "syl.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "feq2d.mm"
include "wral.mm"
include "eqid.mm"
include "fmpt.mm"
include "simpl.mm"
include "wi.mm"
include "cuz.mm"
include "wss.mm"
include "cc.mm"
include "nn0cn.mm"
include "addcom.mm"
include "cz.mm"
include "nn0z.mm"
include "anim1i.mm"
include "ancomd.mm"
include "nn0pzuz.mm"
include "eqeltrd.mm"
include "fzoss2.mm"
include "sselda.mm"
include "weq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "ifbieq12d.mm"
include "rspcv.mm"
include "iftrue.mm"
include "adantl.mm"
include "sylibd.mm"
include "impancom.mm"
include "imp.mm"
include "ralrimiva.mm"
include "iswrdsymb.mm"
include "syl2an2r.mm"
include "simpr.mm"
include "adantr.mm"
include "elincfzoext.mm"
include "syl2anc.mm"
include "nn0cnd.mm"
include "eleq2d.mm"
include "mpbird.mm"
include "cn.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cr.mm"
include "nn0red.mm"
include "elfzoelz.mm"
include "zred.mm"
include "readdcld.mm"
include "ancoms.mm"
include "cle.mm"
include "elfzole1.mm"
include "addge02.mm"
include "mpbid.mm"
include "lensymd.mm"
include "intn3an3d.mm"
include "elfzo0.mm"
include "sylnibr.mm"
include "iffalsed.mm"
include "zcnd.mm"
include "pncan.mm"
include "syl2anr.mm"
include "biimpd.mm"
include "sylbid.mm"
include "syld.mm"
include "jca.mm"
include "ex.mm"
include "syl5bir.mm"
include "syl5.mm"
include "ccatcl.mm"
include "impbid1.mm"

theorem ccatalpha
  let cA: class A
  let cB: class B
  let cS: class S
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. Word _V /\ B e. Word _V ) -> ( ( A ++ B ) e. Word S <-> ( A e. Word S /\ B e. Word S ) ) )

  proof
    cA
    cvv
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    cB
    cconcat
    co
    #
    cS
    cword
    #
    wcel
    #
    cA
    @5
    wcel
    #
    cB
    @5
    wcel
    #
    wa
    #
    @3
    @6
    vx
    cc0
    cA
    chash
    cfv
    #
    cB
    chash
    cfv
    #
    caddc
    co
    #
    cfzo
    co
    #
    vx
    cv
    #
    cc0
    @10
    cfzo
    co
    #
    wcel
    #
    @14
    cA
    cfv
    #
    @14
    @10
    cmin
    co
    #
    cB
    cfv
    #
    cif
    #
    cmpt
    #
    @5
    wcel
    #
    @9
    @3
    @4
    @21
    @5
    vx
    cA
    cB
    @0
    @0
    ccatfval
    eleq1d
    @22
    cc0
    @21
    chash
    cfv
    #
    cfzo
    co
    #
    cS
    @21
    wf
    #
    @3
    @9
    cS
    @21
    wrdf
    @3
    @25
    @13
    cS
    @21
    wf
    #
    @9
    @3
    @24
    @13
    cS
    @21
    @3
    @23
    @12
    cc0
    cfzo
    @3
    @23
    @21
    cdm
    #
    chash
    cfv
    #
    @12
    @3
    @21
    wfun
    #
    @23
    @28
    wceq
    #
    vx
    @13
    @20
    funmpt
    @21
    cfn
    wcel
    #
    @29
    @30
    wb
    @3
    @13
    cfn
    wcel
    @31
    cc0
    @12
    fzofi
    vx
    @13
    @20
    mptfi
    ax-mp
    @21
    hashfun
    mp1i
    mpbii
    @3
    @28
    @13
    chash
    cfv
    #
    @12
    @27
    @13
    chash
    @20
    cvv
    wcel
    #
    @27
    @13
    wceq
    vx
    @13
    vx
    @13
    @20
    cvv
    dmmptg
    @33
    @14
    @13
    wcel
    @16
    @17
    @19
    @14
    cA
    fvex
    @18
    cB
    fvex
    ifex
    a1i
    mprg
    fveq2i
    @3
    @12
    cn0
    wcel
    #
    @32
    @12
    wceq
    @1
    @10
    cn0
    wcel
    #
    @11
    cn0
    wcel
    #
    @34
    @2
    cvv
    cA
    lencl
    #
    cvv
    cB
    lencl
    #
    @10
    @11
    nn0addcl
    syl2an
    @12
    hashfzo0
    syl
    syl5eq
    eqtrd
    oveq2d
    feq2d
    @26
    @20
    cS
    wcel
    #
    vx
    @13
    wral
    #
    @3
    @9
    vx
    @13
    cS
    @20
    @21
    @21
    eqid
    fmpt
    @3
    @40
    @9
    @3
    @40
    wa
    #
    @7
    @8
    @3
    @1
    @40
    vy
    cv
    #
    cA
    cfv
    #
    cS
    wcel
    #
    vy
    @15
    wral
    @7
    @1
    @2
    simpl
    @41
    @44
    vy
    @15
    @41
    @42
    @15
    wcel
    #
    @44
    @3
    @45
    @40
    @44
    @3
    @45
    wa
    #
    @40
    @45
    @43
    @42
    @10
    cmin
    co
    #
    cB
    cfv
    #
    cif
    #
    cS
    wcel
    #
    @44
    @46
    @42
    @13
    wcel
    @40
    @50
    wi
    @3
    @15
    @13
    @42
    @3
    @12
    @10
    cuz
    cfv
    #
    wcel
    #
    @15
    @13
    wss
    @1
    @35
    @36
    @52
    @2
    @37
    @38
    @35
    @36
    wa
    #
    @12
    @11
    @10
    caddc
    co
    #
    @51
    @35
    @10
    cc
    wcel
    #
    @11
    cc
    wcel
    #
    @12
    @54
    wceq
    #
    @36
    @10
    nn0cn
    @11
    nn0cn
    @10
    @11
    addcom
    #
    syl2an
    @53
    @36
    @10
    cz
    wcel
    #
    wa
    @54
    @51
    wcel
    @53
    @59
    @36
    @35
    @59
    @36
    @10
    nn0z
    anim1i
    ancomd
    @11
    @10
    nn0pzuz
    syl
    eqeltrd
    syl2an
    @10
    cc0
    @12
    fzoss2
    syl
    sselda
    @39
    @50
    vx
    @42
    @13
    vx
    vy
    weq
    #
    @20
    @49
    cS
    @60
    @16
    @45
    @17
    @19
    @43
    @48
    @14
    @42
    @15
    eleq1
    @14
    @42
    cA
    fveq2
    @60
    @18
    @47
    cB
    @14
    @42
    @10
    cmin
    oveq1
    fveq2d
    ifbieq12d
    eleq1d
    rspcv
    syl
    @46
    @49
    @43
    cS
    @45
    @49
    @43
    wceq
    @3
    @45
    @43
    @48
    iftrue
    adantl
    eleq1d
    sylibd
    impancom
    imp
    ralrimiva
    vy
    cS
    cA
    iswrdsymb
    syl2an2r
    @3
    @2
    @40
    @42
    cB
    cfv
    #
    cS
    wcel
    #
    vy
    cc0
    @11
    cfzo
    co
    #
    wral
    @8
    @1
    @2
    simpr
    @41
    @62
    vy
    @63
    @41
    @42
    @63
    wcel
    #
    @62
    @3
    @64
    @40
    @62
    @3
    @64
    wa
    #
    @40
    @42
    @10
    caddc
    co
    #
    @15
    wcel
    #
    @66
    cA
    cfv
    #
    @66
    @10
    cmin
    co
    #
    cB
    cfv
    #
    cif
    #
    cS
    wcel
    #
    @62
    @65
    @66
    @13
    wcel
    #
    @40
    @72
    wi
    @65
    @73
    @66
    cc0
    @54
    cfzo
    co
    #
    wcel
    #
    @65
    @64
    @35
    @75
    @3
    @64
    simpr
    @3
    @35
    @64
    @1
    @35
    @2
    @37
    adantr
    adantr
    @10
    cc0
    @11
    @42
    elincfzoext
    syl2anc
    @3
    @73
    @75
    wb
    @64
    @3
    @13
    @74
    @66
    @3
    @12
    @54
    cc0
    cfzo
    @1
    @55
    @56
    @57
    @2
    @1
    @10
    @37
    nn0cnd
    #
    @2
    @11
    @38
    nn0cnd
    @58
    syl2an
    oveq2d
    eleq2d
    adantr
    mpbird
    @39
    @72
    vx
    @66
    @13
    @14
    @66
    wceq
    #
    @20
    @71
    cS
    @77
    @16
    @67
    @17
    @19
    @68
    @70
    @14
    @66
    @15
    eleq1
    @14
    @66
    cA
    fveq2
    @77
    @18
    @69
    cB
    @14
    @66
    @10
    cmin
    oveq1
    fveq2d
    ifbieq12d
    eleq1d
    rspcv
    syl
    @65
    @72
    @70
    cS
    wcel
    #
    @62
    @65
    @71
    @70
    cS
    @65
    @67
    @68
    @70
    @65
    @66
    cn0
    wcel
    #
    @10
    cn
    wcel
    #
    @66
    @10
    clt
    wbr
    #
    w3a
    @67
    @65
    @81
    @79
    @80
    @65
    @10
    @66
    @3
    @10
    cr
    wcel
    #
    @64
    @1
    @82
    @2
    @1
    @10
    @37
    nn0red
    adantr
    #
    adantr
    @64
    @3
    @66
    cr
    wcel
    @64
    @3
    wa
    @42
    @10
    @64
    @42
    cr
    wcel
    #
    @3
    @64
    @42
    @42
    cc0
    @11
    elfzoelz
    #
    zred
    #
    adantr
    @3
    @82
    @64
    @83
    adantl
    readdcld
    ancoms
    @65
    cc0
    @42
    cle
    wbr
    #
    @10
    @66
    cle
    wbr
    #
    @64
    @87
    @3
    @42
    cc0
    @11
    elfzole1
    adantl
    @3
    @82
    @84
    @87
    @88
    wb
    @64
    @83
    @86
    @10
    @42
    addge02
    syl2an
    mpbid
    lensymd
    intn3an3d
    @66
    @10
    elfzo0
    sylnibr
    iffalsed
    eleq1d
    @65
    @78
    @62
    @65
    @70
    @61
    cS
    @65
    @69
    @42
    cB
    @64
    @42
    cc
    wcel
    @55
    @69
    @42
    wceq
    @3
    @64
    @42
    @85
    zcnd
    @1
    @55
    @2
    @76
    adantr
    @42
    @10
    pncan
    syl2anr
    fveq2d
    eleq1d
    biimpd
    sylbid
    syld
    impancom
    imp
    ralrimiva
    vy
    cS
    cB
    iswrdsymb
    syl2an2r
    jca
    ex
    syl5bir
    sylbid
    syl5
    sylbid
    cS
    cA
    cB
    ccatcl
    impbid1
end
