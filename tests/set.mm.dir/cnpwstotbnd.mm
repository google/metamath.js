include "cc.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "ccnfld.mm"
include "cress.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "cprds.mm"
include "cds.mm"
include "cres.mm"
include "ctotbnd.mm"
include "cbnd.mm"
include "cbs.mm"
include "cv.mm"
include "cvv.mm"
include "eqid.mm"
include "fvexd.mm"
include "simpr.mm"
include "wfn.mm"
include "ovex.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "cme.mm"
include "cmt.mm"
include "cnfldms.mm"
include "cnex.mm"
include "ssex.mm"
include "ad2antrr.mm"
include "ressms.mm"
include "sylancr.mm"
include "msmet.mm"
include "syl.mm"
include "wceq.mm"
include "fvconst2.mm"
include "adantl.mm"
include "fveq2d.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "3eltr4d.mm"
include "totbndbnd.mm"
include "wi.mm"
include "cnfldbas.mm"
include "ressbas2.mm"
include "eleqtrrd.mm"
include "bnd2lem.mm"
include "ex.mm"
include "syl5.mm"
include "wb.mm"
include "cabs.mm"
include "cmin.mm"
include "ccom.mm"
include "cntotbnd.mm"
include "a1i.mm"
include "sseq2d.mm"
include "biimpa.mm"
include "xpss12.mm"
include "syl2anc.mm"
include "resabs1d.mm"
include "adantr.mm"
include "cnfldds.mm"
include "ressds.mm"
include "reseq1d.mm"
include "eqtr4d.mm"
include "eleq1d.mm"
include "3bitr4d.mm"
include "pm5.21ndd.mm"
include "prdsbnd2.mm"
include "pwsval.mm"
include "syl5eq.mm"

theorem cnpwstotbnd
  let cA: class A
  let cD: class D
  let cI: class I
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume cnpwstotbnd.y: |- Y = ( ( CCfld |`s A ) ^s I )
  assume cnpwstotbnd.d: |- D = ( ( dist ` Y ) |` ( X X. X ) )


  assert |- ( ( A C_ CC /\ I e. Fin ) -> ( D e. ( TotBnd ` X ) <-> D e. ( Bnd ` X ) ) )

  proof
    cA
    cc
    wss
    #
    cI
    cfn
    wcel
    #
    wa
    #
    ccnfld
    cA
    cress
    co
    #
    csca
    cfv
    #
    cI
    @3
    csn
    cxp
    #
    cprds
    co
    #
    cds
    cfv
    #
    cX
    cX
    cxp
    #
    cres
    #
    cX
    ctotbnd
    cfv
    #
    wcel
    @9
    cX
    cbnd
    cfv
    #
    wcel
    cD
    @10
    wcel
    cD
    @11
    wcel
    @2
    vx
    vy
    cX
    @6
    cbs
    cfv
    #
    @9
    @7
    @5
    @4
    vx
    cv
    #
    @5
    cfv
    #
    cds
    cfv
    #
    @14
    cbs
    cfv
    #
    @16
    cxp
    #
    cres
    #
    cI
    @16
    cvv
    @6
    @6
    eqid
    @12
    eqid
    @16
    eqid
    @18
    eqid
    @7
    eqid
    @2
    @3
    csca
    fvexd
    @0
    @1
    simpr
    #
    @3
    cvv
    wcel
    #
    @5
    cI
    wfn
    @2
    ccnfld
    cA
    cress
    ovex
    #
    cI
    @3
    cvv
    fnconstg
    mp1i
    @9
    eqid
    @2
    @13
    cI
    wcel
    #
    wa
    #
    @3
    cds
    cfv
    #
    @3
    cbs
    cfv
    #
    @25
    cxp
    #
    cres
    #
    @25
    cme
    cfv
    #
    @18
    @16
    cme
    cfv
    @23
    @3
    cmt
    wcel
    #
    @27
    @28
    wcel
    @23
    ccnfld
    cmt
    wcel
    cA
    cvv
    wcel
    #
    @29
    cnfldms
    @0
    @30
    @1
    @22
    cA
    cc
    cnex
    ssex
    ad2antrr
    #
    cA
    ccnfld
    cvv
    ressms
    sylancr
    @27
    @3
    @25
    @25
    eqid
    @27
    eqid
    msmet
    syl
    #
    @23
    @15
    @24
    @17
    @26
    @23
    @14
    @3
    cds
    @22
    @14
    @3
    wceq
    @2
    cI
    @3
    @13
    @21
    fvconst2
    adantl
    #
    fveq2d
    @23
    @16
    @25
    @23
    @14
    @3
    cbs
    @33
    fveq2d
    #
    sqxpeqd
    reseq12d
    #
    @23
    @16
    @25
    cme
    @34
    fveq2d
    3eltr4d
    @23
    @27
    vy
    cv
    #
    @36
    cxp
    #
    cres
    #
    @36
    ctotbnd
    cfv
    #
    wcel
    #
    @38
    @36
    cbnd
    cfv
    #
    wcel
    #
    @18
    @37
    cres
    #
    @39
    wcel
    @43
    @41
    wcel
    @23
    @36
    cA
    wss
    #
    @40
    @42
    @40
    @42
    @23
    @44
    @38
    @36
    totbndbnd
    @23
    @27
    cA
    cme
    cfv
    #
    wcel
    #
    @42
    @44
    wi
    @23
    @27
    @28
    @45
    @32
    @23
    cA
    @25
    cme
    @0
    cA
    @25
    wceq
    @1
    @22
    cA
    cc
    @3
    ccnfld
    @3
    eqid
    #
    cnfldbas
    ressbas2
    ad2antrr
    #
    fveq2d
    eleqtrrd
    @46
    @42
    @44
    @38
    @27
    cA
    @36
    @38
    eqid
    bnd2lem
    ex
    syl
    #
    syl5
    @49
    @23
    @44
    @40
    @42
    wb
    @23
    @44
    wa
    #
    cabs
    cmin
    ccom
    #
    @37
    cres
    #
    @39
    wcel
    #
    @52
    @41
    wcel
    #
    @40
    @42
    @53
    @54
    wb
    @50
    @52
    @36
    @52
    eqid
    cntotbnd
    a1i
    @50
    @38
    @52
    @39
    @50
    @38
    @24
    @37
    cres
    @52
    @50
    @24
    @37
    @26
    @50
    @36
    @25
    wss
    #
    @55
    @37
    @26
    wss
    @23
    @44
    @55
    @23
    cA
    @25
    @36
    @48
    sseq2d
    biimpa
    #
    @56
    @36
    @25
    @36
    @25
    xpss12
    syl2anc
    resabs1d
    @50
    @51
    @24
    @37
    @50
    @30
    @51
    @24
    wceq
    @23
    @30
    @44
    @31
    adantr
    cA
    @51
    ccnfld
    @3
    cvv
    @47
    cnfldds
    ressds
    syl
    reseq1d
    eqtr4d
    #
    eleq1d
    @50
    @38
    @52
    @41
    @57
    eleq1d
    3bitr4d
    ex
    pm5.21ndd
    @23
    @43
    @38
    @39
    @23
    @18
    @27
    @37
    @35
    reseq1d
    #
    eleq1d
    @23
    @43
    @38
    @41
    @58
    eleq1d
    3bitr4d
    prdsbnd2
    @2
    cD
    @9
    @10
    @2
    cD
    cY
    cds
    cfv
    #
    @8
    cres
    @9
    cnpwstotbnd.d
    @2
    @59
    @7
    @8
    @2
    cY
    @6
    cds
    @2
    @20
    @1
    cY
    @6
    wceq
    @21
    @19
    @3
    @4
    cI
    cvv
    cfn
    cY
    cnpwstotbnd.y
    @4
    eqid
    pwsval
    sylancr
    fveq2d
    reseq1d
    syl5eq
    #
    eleq1d
    @2
    cD
    @9
    @11
    @60
    eleq1d
    3bitr4d
end
