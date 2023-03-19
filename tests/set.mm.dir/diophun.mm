include "cdioph.mm"
include "cfv.mm"
include "wcel.mm"
include "cun.mm"
include "cn0.mm"
include "wa.mm"
include "wi.mm"
include "eldiophelnn0.mm"
include "cv.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cres.mm"
include "wceq.mm"
include "cc0.mm"
include "cn.mm"
include "cmap.mm"
include "wrex.mm"
include "cab.mm"
include "cmzp.mm"
include "cvv.mm"
include "cfn.mm"
include "wn.mm"
include "wss.mm"
include "wb.mm"
include "nnex.mm"
include "jctr.mm"
include "cz.mm"
include "1z.mm"
include "nnuz.mm"
include "uzinf.mm"
include "ax-mp.mm"
include "elfznn.mm"
include "ssriv.mm"
include "pm3.2i.mm"
include "eldioph2b.mm"
include "anbi12d.mm"
include "sylancl.mm"
include "reeanv.mm"
include "cmul.mm"
include "cmpt.mm"
include "wo.mm"
include "unab.mm"
include "r19.43.mm"
include "andi.mm"
include "zex.mm"
include "nn0ssz.mm"
include "mapss.mm"
include "mp2an.mm"
include "sseli.mm"
include "adantl.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eqeq1d.mm"
include "wf.mm"
include "simplrl.mm"
include "mzpf.mm"
include "ffvelrnd.mm"
include "zcnd.mm"
include "simplrr.mm"
include "mul0ord.mm"
include "bitr2d.mm"
include "anbi2d.mm"
include "syl5bbr.mm"
include "rexbidva.mm"
include "abbidv.mm"
include "syl5eq.mm"
include "simpl.mm"
include "a1i.mm"
include "simprl.mm"
include "feqmptd.mm"
include "eqeltrrd.mm"
include "simprr.mm"
include "mzpmulmpt.mm"
include "syl2anc.mm"
include "eldioph2.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "uneq12.mm"
include "eleq1d.mm"
include "syl5ibrcom.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "sylbid.mm"
include "anabsi5.mm"

theorem diophun
  let cA: class A
  let cB: class B
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e


  assert |- ( ( A e. ( Dioph ` N ) /\ B e. ( Dioph ` N ) ) -> ( A u. B ) e. ( Dioph ` N ) )

  proof
    cA
    cN
    cdioph
    cfv
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    cB
    cun
    #
    @0
    wcel
    #
    @1
    cN
    cn0
    wcel
    #
    @1
    @2
    wa
    #
    @4
    wi
    cA
    cN
    eldiophelnn0
    @5
    @6
    cA
    vb
    cv
    vd
    cv
    #
    c1
    cN
    cfz
    co
    #
    cres
    wceq
    #
    @7
    va
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vd
    cn0
    cn
    cmap
    co
    #
    wrex
    #
    vb
    cab
    #
    wceq
    #
    va
    cn
    cmzp
    cfv
    #
    wrex
    #
    cB
    @9
    @7
    vc
    cv
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vd
    @14
    wrex
    #
    vb
    cab
    #
    wceq
    #
    vc
    @18
    wrex
    #
    wa
    #
    @4
    @5
    @5
    cn
    cvv
    wcel
    #
    wa
    #
    cn
    cfn
    wcel
    wn
    #
    @8
    cn
    wss
    #
    wa
    #
    @6
    @28
    wb
    @5
    @29
    nnex
    jctr
    @31
    @32
    c1
    cz
    wcel
    @31
    1z
    c1
    cn
    nnuz
    uzinf
    ax-mp
    va
    @8
    cn
    @10
    cN
    elfznn
    ssriv
    #
    pm3.2i
    @30
    @33
    wa
    @1
    @19
    @2
    @27
    vd
    vb
    cA
    cn
    cN
    va
    eldioph2b
    vd
    vb
    cB
    cn
    cN
    vc
    eldioph2b
    anbi12d
    sylancl
    @28
    @17
    @26
    wa
    #
    vc
    @18
    wrex
    va
    @18
    wrex
    @5
    @4
    @17
    @26
    va
    vc
    @18
    @18
    reeanv
    @5
    @35
    @4
    va
    vc
    @18
    @18
    @5
    @10
    @18
    wcel
    #
    @20
    @18
    wcel
    #
    wa
    #
    wa
    #
    @4
    @35
    @16
    @25
    cun
    #
    @0
    wcel
    @39
    @40
    @9
    @7
    ve
    cz
    cn
    cmap
    co
    #
    ve
    cv
    #
    @10
    cfv
    #
    @42
    @20
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    cfv
    #
    cc0
    wceq
    #
    wa
    #
    vd
    @14
    wrex
    #
    vb
    cab
    #
    @0
    @39
    @40
    @15
    @24
    wo
    #
    vb
    cab
    @51
    @15
    @24
    vb
    unab
    @39
    @52
    @50
    vb
    @52
    @13
    @23
    wo
    #
    vd
    @14
    wrex
    @39
    @50
    @13
    @23
    vd
    @14
    r19.43
    @39
    @53
    @49
    vd
    @14
    @53
    @9
    @12
    @22
    wo
    #
    wa
    @39
    @7
    @14
    wcel
    #
    wa
    #
    @49
    @9
    @12
    @22
    andi
    @56
    @54
    @48
    @9
    @56
    @48
    @11
    @21
    cmul
    co
    #
    cc0
    wceq
    @54
    @56
    @47
    @57
    cc0
    @56
    @7
    @41
    wcel
    #
    @47
    @57
    wceq
    @55
    @58
    @39
    @14
    @41
    @7
    cz
    cvv
    wcel
    cn0
    cz
    wss
    @14
    @41
    wss
    zex
    nn0ssz
    cn0
    cz
    cn
    cvv
    mapss
    mp2an
    sseli
    adantl
    #
    ve
    @7
    @45
    @57
    @41
    @46
    @42
    @7
    wceq
    @43
    @11
    @44
    @21
    cmul
    @42
    @7
    @10
    fveq2
    @42
    @7
    @20
    fveq2
    oveq12d
    @46
    eqid
    @11
    @21
    cmul
    ovex
    fvmpt
    syl
    eqeq1d
    @56
    @11
    @21
    @56
    @11
    @56
    @41
    cz
    @7
    @10
    @56
    @36
    @41
    cz
    @10
    wf
    #
    @5
    @36
    @37
    @55
    simplrl
    @10
    cn
    mzpf
    #
    syl
    @59
    ffvelrnd
    zcnd
    @56
    @21
    @56
    @41
    cz
    @7
    @20
    @56
    @37
    @41
    cz
    @20
    wf
    #
    @5
    @36
    @37
    @55
    simplrr
    @20
    cn
    mzpf
    #
    syl
    @59
    ffvelrnd
    zcnd
    mul0ord
    bitr2d
    anbi2d
    syl5bbr
    rexbidva
    syl5bbr
    abbidv
    syl5eq
    @39
    @5
    @29
    @32
    wa
    #
    @46
    @18
    wcel
    #
    @51
    @0
    wcel
    @5
    @38
    simpl
    @64
    @39
    @29
    @32
    nnex
    @34
    pm3.2i
    a1i
    @39
    ve
    @41
    @43
    cmpt
    #
    @18
    wcel
    ve
    @41
    @44
    cmpt
    #
    @18
    wcel
    @65
    @39
    @10
    @66
    @18
    @39
    ve
    @41
    cz
    @10
    @39
    @36
    @60
    @5
    @36
    @37
    simprl
    #
    @61
    syl
    feqmptd
    @68
    eqeltrrd
    @39
    @20
    @67
    @18
    @39
    ve
    @41
    cz
    @20
    @39
    @37
    @62
    @5
    @36
    @37
    simprr
    #
    @63
    syl
    feqmptd
    @69
    eqeltrrd
    ve
    @43
    @44
    cn
    mzpmulmpt
    syl2anc
    vd
    vb
    @46
    cn
    cN
    eldioph2
    syl3anc
    eqeltrd
    @35
    @3
    @40
    @0
    cA
    @16
    cB
    @25
    uneq12
    eleq1d
    syl5ibrcom
    rexlimdvva
    syl5bir
    sylbid
    syl
    anabsi5
end
