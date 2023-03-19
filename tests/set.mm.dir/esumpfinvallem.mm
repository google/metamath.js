include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wf.mm"
include "wa.mm"
include "ccnfld.mm"
include "cress.mm"
include "cgsu.mm"
include "cxrs.mm"
include "cicc.mm"
include "cvv.mm"
include "fex.mm"
include "ancoms.mm"
include "ovexd.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "cc.mm"
include "wss.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "eqid.mm"
include "cnfldbas.mm"
include "ressbas2.mm"
include "ax-mp.mm"
include "cxr.mm"
include "icossxr.mm"
include "xrsbas.mm"
include "eqtr3i.mm"
include "a1i.mm"
include "cv.mm"
include "cplusg.mm"
include "simprl.mm"
include "syl6eleqr.mm"
include "simprr.mm"
include "caddc.mm"
include "ge0addcl.mm"
include "ovex.mm"
include "cnfldadd.mm"
include "ressplusg.mm"
include "oveqi.mm"
include "3eltr3g.mm"
include "syl2anc.mm"
include "cxad.mm"
include "simpl.mm"
include "sseldi.mm"
include "simpr.mm"
include "rexadd.mm"
include "eqcomd.mm"
include "xrsadd.mm"
include "3eqtr3g.mm"
include "wfun.mm"
include "ffun.mm"
include "syl.mm"
include "crn.mm"
include "frn.mm"
include "syl6sseq.mm"
include "gsumpropd2.mm"
include "cnfldex.mm"
include "0e0icopnf.mm"
include "addid2d.mm"
include "addid1d.mm"
include "jca.mm"
include "gsumress.mm"
include "xrge0base.mm"
include "xrge0plusg.mm"
include "cin.mm"
include "ressress.mm"
include "mp2an.mm"
include "incom.mm"
include "icossicc.mm"
include "dfss.mm"
include "mpbi.mm"
include "eqtr4i.mm"
include "oveq2i.mm"
include "eqtr2i.mm"
include "iccssxr.mm"
include "xaddid2.mm"
include "xaddid1.mm"
include "3eqtr4d.mm"

theorem esumpfinvallem
  let cA: class A
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. V /\ F : A --> ( 0 [,) +oo ) ) -> ( CCfld gsum F ) = ( ( RR*s |`s ( 0 [,] +oo ) ) gsum F ) )

  proof
    cA
    cV
    wcel
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
    wa
    #
    ccnfld
    @1
    cress
    co
    #
    cF
    cgsu
    co
    cxrs
    @1
    cress
    co
    #
    cF
    cgsu
    co
    ccnfld
    cF
    cgsu
    co
    cxrs
    cc0
    cpnf
    cicc
    co
    #
    cress
    co
    #
    cF
    cgsu
    co
    @3
    vy
    cF
    @4
    @5
    cvv
    cvv
    cvv
    vx
    @2
    @0
    cF
    cvv
    wcel
    cA
    @1
    cV
    cF
    fex
    ancoms
    @3
    ccnfld
    @1
    cress
    ovexd
    @3
    cxrs
    @1
    cress
    ovexd
    @4
    cbs
    cfv
    #
    @5
    cbs
    cfv
    #
    wceq
    @3
    @1
    @8
    @9
    @1
    cc
    wss
    #
    @1
    @8
    wceq
    @1
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    #
    @1
    cc
    @4
    ccnfld
    @4
    eqid
    #
    cnfldbas
    ressbas2
    ax-mp
    #
    @1
    cxr
    wss
    @1
    @9
    wceq
    cc0
    cpnf
    icossxr
    @1
    cxr
    @5
    cxrs
    @5
    eqid
    #
    xrsbas
    ressbas2
    ax-mp
    eqtr3i
    a1i
    @3
    vx
    cv
    #
    @8
    wcel
    #
    vy
    cv
    #
    @8
    wcel
    #
    wa
    wa
    #
    @15
    @1
    wcel
    #
    @17
    @1
    wcel
    #
    @15
    @17
    @4
    cplusg
    cfv
    #
    co
    #
    @8
    wcel
    @19
    @15
    @8
    @1
    @3
    @16
    @18
    simprl
    @13
    syl6eleqr
    #
    @19
    @17
    @8
    @1
    @3
    @16
    @18
    simprr
    @13
    syl6eleqr
    #
    @20
    @21
    wa
    #
    @15
    @17
    caddc
    co
    #
    @1
    @23
    @8
    @15
    @17
    ge0addcl
    caddc
    @22
    @15
    @17
    @1
    cvv
    wcel
    #
    caddc
    @22
    wceq
    cc0
    cpnf
    cico
    ovex
    #
    @1
    caddc
    ccnfld
    @4
    cvv
    @12
    cnfldadd
    ressplusg
    ax-mp
    oveqi
    #
    @13
    3eltr3g
    syl2anc
    @19
    @20
    @21
    @23
    @15
    @17
    @5
    cplusg
    cfv
    #
    co
    #
    wceq
    @24
    @25
    @26
    @27
    @15
    @17
    cxad
    co
    #
    @23
    @32
    @26
    @15
    cr
    wcel
    #
    @17
    cr
    wcel
    #
    @27
    @33
    wceq
    @26
    @1
    cr
    @15
    rge0ssre
    @20
    @21
    simpl
    sseldi
    @26
    @1
    cr
    @17
    rge0ssre
    @20
    @21
    simpr
    sseldi
    @34
    @35
    wa
    @33
    @27
    @15
    @17
    rexadd
    eqcomd
    syl2anc
    @30
    cxad
    @31
    @15
    @17
    @28
    cxad
    @31
    wceq
    @29
    @1
    cxad
    cxrs
    @5
    cvv
    @14
    xrsadd
    ressplusg
    ax-mp
    oveqi
    3eqtr3g
    syl2anc
    @3
    @2
    cF
    wfun
    @0
    @2
    simpr
    #
    cA
    @1
    cF
    ffun
    syl
    @3
    cF
    crn
    #
    @1
    @8
    @3
    @2
    @37
    @1
    wss
    @36
    cA
    @1
    cF
    frn
    syl
    @13
    syl6sseq
    gsumpropd2
    @3
    vx
    cA
    cc
    caddc
    @1
    cF
    ccnfld
    @4
    cvv
    cV
    cc0
    cnfldbas
    cnfldadd
    @12
    ccnfld
    cvv
    wcel
    @3
    cnfldex
    a1i
    @0
    @2
    simpl
    #
    @10
    @3
    @11
    a1i
    @36
    cc0
    @1
    wcel
    @3
    0e0icopnf
    a1i
    #
    @3
    @15
    cc
    wcel
    #
    wa
    #
    cc0
    @15
    caddc
    co
    @15
    wceq
    @15
    cc0
    caddc
    co
    @15
    wceq
    @41
    @15
    @3
    @40
    simpr
    #
    addid2d
    @41
    @15
    @42
    addid1d
    jca
    gsumress
    @3
    vx
    cA
    @6
    cxad
    @1
    cF
    @7
    @5
    cvv
    cV
    cc0
    xrge0base
    xrge0plusg
    @7
    @1
    cress
    co
    #
    cxrs
    @6
    @1
    cin
    #
    cress
    co
    #
    @5
    @6
    cvv
    wcel
    @28
    @43
    @45
    wceq
    cc0
    cpnf
    cicc
    ovex
    @29
    @6
    @1
    cxrs
    cvv
    cvv
    ressress
    mp2an
    @44
    @1
    cxrs
    cress
    @44
    @1
    @6
    cin
    #
    @1
    @6
    @1
    incom
    @1
    @6
    wss
    #
    @1
    @46
    wceq
    cc0
    cpnf
    icossicc
    #
    @1
    @6
    dfss
    mpbi
    eqtr4i
    oveq2i
    eqtr2i
    @3
    cxrs
    @6
    cress
    ovexd
    @38
    @47
    @3
    @48
    a1i
    @36
    @39
    @3
    @15
    @6
    wcel
    #
    wa
    #
    cc0
    @15
    cxad
    co
    @15
    wceq
    #
    @15
    cc0
    cxad
    co
    @15
    wceq
    #
    @50
    @15
    cxr
    wcel
    #
    @51
    @50
    @6
    cxr
    @15
    cc0
    cpnf
    iccssxr
    @3
    @49
    simpr
    sseldi
    #
    @15
    xaddid2
    syl
    @50
    @53
    @52
    @54
    @15
    xaddid1
    syl
    jca
    gsumress
    3eqtr4d
end
