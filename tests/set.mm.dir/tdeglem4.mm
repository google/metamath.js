include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "csn.mm"
include "cxp.mm"
include "cv.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "wne.mm"
include "rexnal.mm"
include "df-ne.mm"
include "ccnfld.mm"
include "cdif.mm"
include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "caddc.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "ad2antlr.mm"
include "cn0.mm"
include "psrbagf.mm"
include "feqmptd.mm"
include "adantr.mm"
include "oveq2d.mm"
include "cc.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cnfldadd.mm"
include "crg.mm"
include "ccmn.mm"
include "cnring.mm"
include "ringcmn.mm"
include "mp1i.mm"
include "simpll.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "nn0cnd.mm"
include "cfsupp.mm"
include "wbr.mm"
include "psrbagfsupp.mm"
include "ancoms.mm"
include "eqbrtrrd.mm"
include "cin.mm"
include "c0.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "a1i.mm"
include "cun.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "ad2antrl.mm"
include "gsumsplit2.mm"
include "3eqtrd.mm"
include "cn.mm"
include "cvv.mm"
include "difexg.mm"
include "ad2antrr.mm"
include "csubmnd.mm"
include "nn0subm.mm"
include "eldifi.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "eqid.mm"
include "fmptd.mm"
include "wfun.mm"
include "csupp.mm"
include "wss.mm"
include "mptexg.mm"
include "syl.mm"
include "funmpt.mm"
include "cres.mm"
include "difss.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "resss.mm"
include "eqsstr3i.mm"
include "funsssuppss.mm"
include "syl3anc.mm"
include "fsuppsssupp.mm"
include "syl22anc.mm"
include "gsumsubmcl.mm"
include "cmnd.mm"
include "ringmnd.mm"
include "simprl.mm"
include "ffvelrnd.mm"
include "fveq2.mm"
include "gsumsn.mm"
include "wo.mm"
include "simprr.mm"
include "sylib.mm"
include "elnn0.mm"
include "orel2.mm"
include "sylc.mm"
include "eqeltrd.mm"
include "nn0nnaddcl.mm"
include "syl2anc.mm"
include "nnne0d.mm"
include "eqnetrd.mm"
include "expr.mm"
include "syl5bir.mm"
include "rexlimdva.mm"
include "necon4bd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "0nn0.mm"
include "fnconstg.mm"
include "eqfnfv.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "eqeq2d.mm"
include "ralbiia.mm"
include "syl6bb.mm"
include "sylibrd.mm"
include "psrbag0.mm"
include "fconstmpt.mm"
include "oveq2i.mm"
include "gsumz.mm"
include "mpan.mm"
include "syl5eq.mm"
include "eqtrd.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem tdeglem4
  let cA: class A
  let vh: setvar h
  let vm: setvar m
  let cH: class H
  let cI: class I
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cY: class Y
  assume tdeglem.a: |- A = { m e. ( NN0 ^m I ) | ( `' m " NN ) e. Fin }
  assume tdeglem.h: |- H = ( h e. A |-> ( CCfld gsum h ) )

  disjoint A h
  disjoint I h
  disjoint I m
  disjoint h m
  disjoint V h
  disjoint X h
  disjoint X m
  disjoint A x
  disjoint A y
  disjoint h x
  disjoint h y
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint V x
  disjoint V y
  disjoint Y h
  disjoint Y m
  disjoint H x
  disjoint X x
  disjoint X y
  assert |- ( ( I e. V /\ X e. A ) -> ( ( H ` X ) = 0 <-> X = ( I X. { 0 } ) ) )

  proof
    cI
    cV
    wcel
    #
    cX
    cA
    wcel
    #
    wa
    #
    cX
    cH
    cfv
    #
    cc0
    wceq
    #
    cX
    cI
    cc0
    csn
    cxp
    #
    wceq
    #
    @2
    @4
    vx
    cv
    #
    cX
    cfv
    #
    cc0
    wceq
    #
    vx
    cI
    wral
    #
    @6
    @2
    @10
    @3
    cc0
    @10
    wn
    @9
    wn
    #
    vx
    cI
    wrex
    @2
    @3
    cc0
    wne
    #
    @9
    vx
    cI
    rexnal
    @2
    @11
    @12
    vx
    cI
    @11
    @8
    cc0
    wne
    #
    @2
    @7
    cI
    wcel
    #
    wa
    @12
    @8
    cc0
    df-ne
    #
    @2
    @14
    @13
    @12
    @2
    @14
    @13
    wa
    #
    wa
    #
    @3
    ccnfld
    vy
    cI
    @7
    csn
    #
    cdif
    #
    vy
    cv
    #
    cX
    cfv
    #
    cmpt
    #
    cgsu
    co
    #
    ccnfld
    vy
    @18
    @21
    cmpt
    cgsu
    co
    #
    caddc
    co
    #
    cc0
    @17
    @3
    ccnfld
    cX
    cgsu
    co
    #
    ccnfld
    vy
    cI
    @21
    cmpt
    #
    cgsu
    co
    @25
    @1
    @3
    @26
    wceq
    @0
    @16
    vh
    cX
    ccnfld
    vh
    cv
    #
    cgsu
    co
    #
    @26
    cA
    cH
    @28
    cX
    ccnfld
    cgsu
    oveq2
    tdeglem.h
    ccnfld
    cX
    cgsu
    ovex
    fvmpt
    ad2antlr
    @17
    cX
    @27
    ccnfld
    cgsu
    @2
    cX
    @27
    wceq
    @16
    @2
    vy
    cI
    cn0
    cX
    cA
    vm
    cX
    cI
    cV
    tdeglem.a
    psrbagf
    #
    feqmptd
    adantr
    #
    oveq2d
    @17
    cI
    cc
    @19
    @18
    caddc
    vy
    ccnfld
    cV
    @21
    cc0
    cnfldbas
    cnfld0
    cnfldadd
    ccnfld
    crg
    wcel
    #
    ccnfld
    ccmn
    wcel
    @17
    cnring
    ccnfld
    ringcmn
    mp1i
    #
    @0
    @1
    @16
    simpll
    @17
    @20
    cI
    wcel
    #
    wa
    @21
    @17
    cI
    cn0
    @20
    cX
    @2
    cI
    cn0
    cX
    wf
    #
    @16
    @30
    adantr
    #
    ffvelrnda
    nn0cnd
    @17
    cX
    @27
    cc0
    cfsupp
    @31
    @2
    cX
    cc0
    cfsupp
    wbr
    #
    @16
    @1
    @0
    @37
    cA
    vm
    cI
    cV
    cX
    tdeglem.a
    psrbagfsupp
    ancoms
    adantr
    eqbrtrrd
    #
    @19
    @18
    cin
    #
    c0
    wceq
    @17
    @39
    @18
    @19
    cin
    c0
    @19
    @18
    incom
    @18
    cI
    disjdif
    eqtri
    a1i
    @14
    cI
    @19
    @18
    cun
    #
    wceq
    @2
    @13
    @14
    @40
    cI
    cI
    @7
    difsnid
    eqcomd
    ad2antrl
    gsumsplit2
    3eqtrd
    @17
    @25
    @17
    @23
    cn0
    wcel
    @24
    cn
    wcel
    @25
    cn
    wcel
    @17
    @19
    cn0
    @22
    ccnfld
    cvv
    cc0
    cnfld0
    @33
    @0
    @19
    cvv
    wcel
    #
    @1
    @16
    cI
    @18
    cV
    difexg
    #
    ad2antrr
    cn0
    ccnfld
    csubmnd
    cfv
    wcel
    @17
    nn0subm
    a1i
    @17
    vy
    @19
    @21
    cn0
    @22
    @17
    @35
    @34
    @21
    cn0
    wcel
    @20
    @19
    wcel
    @36
    @20
    cI
    @18
    eldifi
    cI
    cn0
    @20
    cX
    ffvelrn
    syl2an
    @22
    eqid
    fmptd
    @17
    @22
    cvv
    wcel
    #
    @22
    wfun
    #
    @27
    cc0
    cfsupp
    wbr
    @22
    cc0
    csupp
    co
    @27
    cc0
    csupp
    co
    wss
    #
    @22
    cc0
    cfsupp
    wbr
    @0
    @43
    @1
    @16
    @0
    @41
    @43
    @42
    vy
    @19
    @21
    cvv
    mptexg
    syl
    ad2antrr
    @44
    @17
    vy
    @19
    @21
    funmpt
    a1i
    @38
    @17
    @27
    wfun
    #
    @22
    @27
    wss
    #
    @27
    cvv
    wcel
    #
    @45
    @46
    @17
    vy
    cI
    @21
    funmpt
    a1i
    @47
    @17
    @22
    @27
    @19
    cres
    #
    @27
    @19
    cI
    wss
    @49
    @22
    wceq
    cI
    @18
    difss
    vy
    cI
    @19
    @21
    resmpt
    ax-mp
    @27
    @19
    resss
    eqsstr3i
    a1i
    @0
    @48
    @1
    @16
    vy
    cI
    @21
    cV
    mptexg
    ad2antrr
    @22
    @27
    cvv
    cc0
    funsssuppss
    syl3anc
    @27
    @22
    cvv
    cc0
    fsuppsssupp
    syl22anc
    gsumsubmcl
    @17
    @24
    @8
    cn
    @17
    ccnfld
    cmnd
    wcel
    #
    @14
    @8
    cc
    wcel
    @24
    @8
    wceq
    @32
    @50
    @17
    cnring
    ccnfld
    ringmnd
    #
    mp1i
    @2
    @14
    @13
    simprl
    #
    @17
    @8
    @17
    cI
    cn0
    @7
    cX
    @36
    @52
    ffvelrnd
    #
    nn0cnd
    @21
    cc
    @8
    vy
    ccnfld
    @7
    cI
    cnfldbas
    @20
    @7
    cX
    fveq2
    gsumsn
    syl3anc
    @17
    @11
    @8
    cn
    wcel
    #
    @9
    wo
    #
    @54
    @17
    @13
    @11
    @2
    @14
    @13
    simprr
    @15
    sylib
    @17
    @8
    cn0
    wcel
    @55
    @53
    @8
    elnn0
    sylib
    @9
    @54
    orel2
    sylc
    eqeltrd
    @23
    @24
    nn0nnaddcl
    syl2anc
    nnne0d
    eqnetrd
    expr
    syl5bir
    rexlimdva
    syl5bir
    necon4bd
    @2
    @6
    @8
    @7
    @5
    cfv
    #
    wceq
    #
    vx
    cI
    wral
    #
    @10
    @2
    cX
    cI
    wfn
    #
    @5
    cI
    wfn
    #
    @6
    @58
    wb
    @2
    @35
    @59
    @30
    cI
    cn0
    cX
    ffn
    syl
    cc0
    cn0
    wcel
    @60
    @2
    0nn0
    cI
    cc0
    cn0
    fnconstg
    mp1i
    vx
    cI
    cX
    @5
    eqfnfv
    syl2anc
    @57
    @9
    vx
    cI
    @14
    @56
    cc0
    @8
    cI
    cc0
    @7
    c0ex
    fvconst2
    eqeq2d
    ralbiia
    syl6bb
    sylibrd
    @2
    @4
    @6
    @5
    cH
    cfv
    #
    cc0
    wceq
    @2
    @61
    ccnfld
    @5
    cgsu
    co
    #
    cc0
    @2
    @5
    cA
    wcel
    #
    @61
    @62
    wceq
    @0
    @63
    @1
    cA
    vm
    cI
    cV
    tdeglem.a
    psrbag0
    adantr
    vh
    @5
    @29
    @62
    cA
    cH
    @28
    @5
    ccnfld
    cgsu
    oveq2
    tdeglem.h
    ccnfld
    @5
    cgsu
    ovex
    fvmpt
    syl
    @2
    @62
    ccnfld
    vx
    cI
    cc0
    cmpt
    #
    cgsu
    co
    #
    cc0
    @5
    @64
    ccnfld
    cgsu
    vx
    cI
    cc0
    fconstmpt
    oveq2i
    @0
    @65
    cc0
    wceq
    #
    @1
    @50
    @0
    @66
    @32
    @50
    cnring
    @51
    ax-mp
    cI
    vx
    ccnfld
    cV
    cc0
    cnfld0
    gsumz
    mpan
    adantr
    syl5eq
    eqtrd
    @6
    @3
    @61
    cc0
    cX
    @5
    cH
    fveq2
    eqeq1d
    syl5ibrcom
    impbid
end
