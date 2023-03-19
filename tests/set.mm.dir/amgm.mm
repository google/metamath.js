include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "cgsu.mm"
include "c1.mm"
include "chash.mm"
include "cdiv.mm"
include "ccxp.mm"
include "ccnfld.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "csn.mm"
include "cres.mm"
include "cdif.mm"
include "cmul.mm"
include "cc.mm"
include "cnfldbas.mm"
include "mgpbas.mm"
include "cnfld1.mm"
include "ringidval.mm"
include "cnfldmul.mm"
include "mgpplusg.mm"
include "ccrg.mm"
include "ccmn.mm"
include "cncrng.mm"
include "crngmgp.mm"
include "mp1i.mm"
include "simpl1.mm"
include "wss.mm"
include "simpl3.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "fss.mm"
include "sylancl.mm"
include "cvv.mm"
include "1ex.mm"
include "a1i.mm"
include "fdmfifsupp.mm"
include "cin.mm"
include "disjdif.mm"
include "cun.mm"
include "undif2.mm"
include "simprl.mm"
include "snssd.mm"
include "ssequn1.mm"
include "sylib.mm"
include "syl5req.mm"
include "gsumsplit.mm"
include "cmpt.mm"
include "feqresmpt.mm"
include "oveq2d.mm"
include "cmnd.mm"
include "crg.mm"
include "cnring.mm"
include "ringmgp.mm"
include "ffvelrnd.mm"
include "fveq2.mm"
include "gsumsn.mm"
include "syl3anc.mm"
include "simprr.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "diffi.mm"
include "syl.mm"
include "difss.mm"
include "fssres.mm"
include "gsumcl.mm"
include "mul02d.mm"
include "cn.mm"
include "simpl2.mm"
include "wb.mm"
include "hashnncl.mm"
include "mpbird.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "reccld.mm"
include "recne0d.mm"
include "0cxpd.mm"
include "eqtrd.mm"
include "clt.mm"
include "cnfld0.mm"
include "ringcmn.mm"
include "csubmnd.mm"
include "rege0subm.mm"
include "c0ex.mm"
include "gsumsubmcl.mm"
include "elrege0.mm"
include "nnred.mm"
include "nngt0d.mm"
include "divge0.mm"
include "syl12anc.mm"
include "eqbrtrd.mm"
include "rexlimdvaa.mm"
include "wn.mm"
include "wral.mm"
include "ralnex.mm"
include "wfn.mm"
include "crp.mm"
include "ffn.mm"
include "wo.mm"
include "ffvelrn.mm"
include "3ad2antl3.mm"
include "simprd.mm"
include "0re.mm"
include "simpld.mm"
include "leloe.mm"
include "sylancr.mm"
include "mpbid.mm"
include "ord.mm"
include "eqcom.mm"
include "syl6ib.mm"
include "con1d.mm"
include "elrp.mm"
include "baib.mm"
include "sylibrd.mm"
include "ralimdva.mm"
include "imp.mm"
include "ffnfv.mm"
include "sylanbrc.mm"
include "amgmlem.mm"
include "ex.mm"
include "syl5bir.mm"
include "pm2.61d.mm"

theorem amgm
  let cA: class A
  let cF: class F
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vk: setvar k
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vt: setvar t
  let wph: wff ph
  assume amgm.1: |- M = ( mulGrp ` CCfld )


  assert |- ( ( A e. Fin /\ A =/= (/) /\ F : A --> ( 0 [,) +oo ) ) -> ( ( M gsum F ) ^c ( 1 / ( # ` A ) ) ) <_ ( ( CCfld gsum F ) / ( # ` A ) ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    cA
    cc0
    cpnf
    cico
    co
    #
    cF
    wf
    #
    w3a
    #
    vx
    cv
    #
    cF
    cfv
    #
    cc0
    wceq
    #
    vx
    cA
    wrex
    #
    cM
    cF
    cgsu
    co
    #
    c1
    cA
    chash
    cfv
    #
    cdiv
    co
    #
    ccxp
    co
    #
    ccnfld
    cF
    cgsu
    co
    #
    @10
    cdiv
    co
    #
    cle
    wbr
    #
    @4
    @7
    @15
    vx
    cA
    @4
    @5
    cA
    wcel
    #
    @7
    wa
    #
    wa
    #
    @12
    cc0
    @14
    cle
    @18
    @12
    cc0
    @11
    ccxp
    co
    cc0
    @18
    @9
    cc0
    @11
    ccxp
    @18
    @9
    cM
    cF
    @5
    csn
    #
    cres
    #
    cgsu
    co
    #
    cM
    cF
    cA
    @19
    cdif
    #
    cres
    #
    cgsu
    co
    #
    cmul
    co
    cc0
    @24
    cmul
    co
    cc0
    @18
    cA
    cc
    @19
    @22
    cmul
    cF
    cM
    cfn
    c1
    cc
    ccnfld
    cM
    amgm.1
    cnfldbas
    mgpbas
    #
    ccnfld
    c1
    cM
    amgm.1
    cnfld1
    ringidval
    #
    ccnfld
    cmul
    cM
    amgm.1
    cnfldmul
    mgpplusg
    ccnfld
    ccrg
    wcel
    cM
    ccmn
    wcel
    @18
    cncrng
    ccnfld
    cM
    amgm.1
    crngmgp
    mp1i
    #
    @0
    @1
    @3
    @17
    simpl1
    #
    @18
    @3
    @2
    cc
    wss
    cA
    cc
    cF
    wf
    #
    @0
    @1
    @3
    @17
    simpl3
    #
    @2
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    cA
    @2
    cc
    cF
    fss
    sylancl
    #
    @18
    cA
    cc
    cF
    cvv
    c1
    @31
    @28
    c1
    cvv
    wcel
    @18
    1ex
    a1i
    #
    fdmfifsupp
    @19
    @22
    cin
    c0
    wceq
    @18
    @19
    cA
    disjdif
    a1i
    @18
    @19
    @22
    cun
    @19
    cA
    cun
    #
    cA
    @19
    cA
    undif2
    @18
    @19
    cA
    wss
    @33
    cA
    wceq
    @18
    @5
    cA
    @4
    @16
    @7
    simprl
    #
    snssd
    #
    @19
    cA
    ssequn1
    sylib
    syl5req
    gsumsplit
    @18
    @21
    cc0
    @24
    cmul
    @18
    @21
    cM
    vy
    @19
    vy
    cv
    #
    cF
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    @6
    cc0
    @18
    @20
    @38
    cM
    cgsu
    @18
    vy
    cA
    @2
    @19
    cF
    @30
    @35
    feqresmpt
    oveq2d
    @18
    cM
    cmnd
    wcel
    #
    @16
    @6
    cc
    wcel
    @39
    @6
    wceq
    ccnfld
    crg
    wcel
    #
    @40
    @18
    cnring
    ccnfld
    cM
    amgm.1
    ringmgp
    mp1i
    @34
    @18
    cA
    cc
    @5
    cF
    @31
    @34
    ffvelrnd
    @37
    cc
    @6
    vy
    cM
    @5
    cA
    @25
    @36
    @5
    cF
    fveq2
    gsumsn
    syl3anc
    @4
    @16
    @7
    simprr
    3eqtrd
    oveq1d
    @18
    @24
    @18
    @22
    cc
    @23
    cM
    cfn
    c1
    @25
    @26
    @27
    @18
    @0
    @22
    cfn
    wcel
    @28
    cA
    @19
    diffi
    syl
    #
    @18
    @29
    @22
    cA
    wss
    @22
    cc
    @23
    wf
    @31
    cA
    @19
    difss
    cA
    cc
    @22
    cF
    fssres
    sylancl
    #
    @18
    @22
    cc
    @23
    cvv
    c1
    @43
    @42
    @32
    fdmfifsupp
    gsumcl
    mul02d
    3eqtrd
    oveq1d
    @18
    @11
    @18
    @10
    @18
    @10
    @18
    @10
    cn
    wcel
    #
    @1
    @0
    @1
    @3
    @17
    simpl2
    @18
    @0
    @44
    @1
    wb
    @28
    cA
    hashnncl
    syl
    mpbird
    #
    nncnd
    #
    @18
    @10
    @45
    nnne0d
    #
    reccld
    @18
    @10
    @46
    @47
    recne0d
    0cxpd
    eqtrd
    @18
    @13
    cr
    wcel
    cc0
    @13
    cle
    wbr
    wa
    #
    @10
    cr
    wcel
    cc0
    @10
    clt
    wbr
    cc0
    @14
    cle
    wbr
    @18
    @13
    @2
    wcel
    @48
    @18
    cA
    @2
    cF
    ccnfld
    cfn
    cc0
    cnfld0
    @41
    ccnfld
    ccmn
    wcel
    @18
    cnring
    ccnfld
    ringcmn
    mp1i
    @28
    @2
    ccnfld
    csubmnd
    cfv
    wcel
    @18
    rege0subm
    a1i
    @30
    @18
    cA
    @2
    cF
    cvv
    cc0
    @30
    @28
    cc0
    cvv
    wcel
    @18
    c0ex
    a1i
    fdmfifsupp
    gsumsubmcl
    @13
    elrege0
    sylib
    @18
    @10
    @45
    nnred
    @18
    @10
    @45
    nngt0d
    @13
    @10
    divge0
    syl12anc
    eqbrtrd
    rexlimdvaa
    @8
    wn
    @7
    wn
    #
    vx
    cA
    wral
    #
    @4
    @15
    @7
    vx
    cA
    ralnex
    @4
    @50
    @15
    @4
    @50
    wa
    #
    cA
    cF
    cM
    amgm.1
    @0
    @1
    @3
    @50
    simpl1
    @0
    @1
    @3
    @50
    simpl2
    @51
    cF
    cA
    wfn
    #
    @6
    crp
    wcel
    #
    vx
    cA
    wral
    #
    cA
    crp
    cF
    wf
    @51
    @3
    @52
    @0
    @1
    @3
    @50
    simpl3
    cA
    @2
    cF
    ffn
    syl
    @4
    @50
    @54
    @4
    @49
    @53
    vx
    cA
    @4
    @16
    wa
    #
    @49
    cc0
    @6
    clt
    wbr
    #
    @53
    @55
    @56
    @7
    @55
    @56
    wn
    cc0
    @6
    wceq
    #
    @7
    @55
    @56
    @57
    @55
    cc0
    @6
    cle
    wbr
    #
    @56
    @57
    wo
    #
    @55
    @6
    cr
    wcel
    #
    @58
    @55
    @6
    @2
    wcel
    #
    @60
    @58
    wa
    @3
    @0
    @16
    @61
    @1
    cA
    @2
    @5
    cF
    ffvelrn
    3ad2antl3
    @6
    elrege0
    sylib
    #
    simprd
    @55
    cc0
    cr
    wcel
    @60
    @58
    @59
    wb
    0re
    @55
    @60
    @58
    @62
    simpld
    #
    cc0
    @6
    leloe
    sylancr
    mpbid
    ord
    cc0
    @6
    eqcom
    syl6ib
    con1d
    @55
    @60
    @53
    @56
    wb
    @63
    @53
    @60
    @56
    @6
    elrp
    baib
    syl
    sylibrd
    ralimdva
    imp
    vx
    cA
    crp
    cF
    ffnfv
    sylanbrc
    amgmlem
    ex
    syl5bir
    pm2.61d
end
