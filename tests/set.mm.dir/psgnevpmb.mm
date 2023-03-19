include "cfn.mm"
include "wcel.mm"
include "cevpm.mm"
include "cfv.mm"
include "ccnv.mm"
include "c1.mm"
include "csn.mm"
include "cima.mm"
include "wceq.mm"
include "wa.mm"
include "cvv.mm"
include "elex.mm"
include "cv.mm"
include "cpsgn.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "df-evpm.mm"
include "fvex.mm"
include "eqeltri.mm"
include "cnvex.mm"
include "imaex.mm"
include "fvmpt.mm"
include "syl.mm"
include "eleq2d.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cneg.mm"
include "cpr.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "wf.mm"
include "wfn.mm"
include "wb.mm"
include "cghm.mm"
include "eqid.mm"
include "psgnghm2.mm"
include "ghmf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "3syl.mm"
include "bitrd.mm"

theorem psgnevpmb
  let cD: class D
  let cP: class P
  let cS: class S
  let cF: class F
  let cN: class N
  let vd: setvar d
  assume evpmss.s: |- S = ( SymGrp ` D )
  assume evpmss.p: |- P = ( Base ` S )
  assume psgnevpmb.n: |- N = ( pmSgn ` D )


  assert |- ( D e. Fin -> ( F e. ( pmEven ` D ) <-> ( F e. P /\ ( N ` F ) = 1 ) ) )

  proof
    cD
    cfn
    wcel
    #
    cF
    cD
    cevpm
    cfv
    #
    wcel
    cF
    cN
    ccnv
    #
    c1
    csn
    #
    cima
    #
    wcel
    #
    cF
    cP
    wcel
    cF
    cN
    cfv
    c1
    wceq
    wa
    #
    @0
    @1
    @4
    cF
    @0
    cD
    cvv
    wcel
    @1
    @4
    wceq
    cD
    cfn
    elex
    vd
    cD
    vd
    cv
    #
    cpsgn
    cfv
    #
    ccnv
    #
    @3
    cima
    @4
    cvv
    cevpm
    @7
    cD
    wceq
    #
    @9
    @2
    @3
    @10
    @8
    cN
    @10
    @8
    cD
    cpsgn
    cfv
    #
    cN
    @7
    cD
    cpsgn
    fveq2
    psgnevpmb.n
    syl6eqr
    cnveqd
    imaeq1d
    vd
    df-evpm
    @2
    @3
    cN
    cN
    @11
    cvv
    psgnevpmb.n
    cD
    cpsgn
    fvex
    eqeltri
    cnvex
    imaex
    fvmpt
    syl
    eleq2d
    @0
    cP
    ccnfld
    cmgp
    cfv
    c1
    c1
    cneg
    cpr
    cress
    co
    #
    cbs
    cfv
    #
    cN
    wf
    #
    cN
    cP
    wfn
    @5
    @6
    wb
    @0
    cN
    cS
    @12
    cghm
    co
    wcel
    @14
    cD
    cS
    @12
    cN
    evpmss.s
    psgnevpmb.n
    @12
    eqid
    psgnghm2
    cS
    @12
    cN
    cP
    @13
    evpmss.p
    @13
    eqid
    ghmf
    syl
    cP
    @13
    cN
    ffn
    cP
    c1
    cF
    cN
    fniniseg
    3syl
    bitrd
end
