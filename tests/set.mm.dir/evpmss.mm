include "cvv.mm"
include "wcel.mm"
include "cevpm.mm"
include "cfv.mm"
include "wss.mm"
include "cpsgn.mm"
include "ccnv.mm"
include "c1.mm"
include "csn.mm"
include "cima.mm"
include "cv.mm"
include "wceq.mm"
include "fveq2.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "df-evpm.mm"
include "fvex.mm"
include "cnvex.mm"
include "imaex.mm"
include "fvmpt.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cress.mm"
include "co.mm"
include "cbs.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "cneg.mm"
include "cpr.mm"
include "cghm.mm"
include "wf.mm"
include "eqid.mm"
include "psgnghm.mm"
include "ghmf.mm"
include "fdm.mm"
include "3syl.mm"
include "ressbasss.mm"
include "syl6eqss.mm"
include "syl5ss.mm"
include "eqsstrd.mm"
include "wn.mm"
include "c0.mm"
include "fvprc.mm"
include "0ss.mm"
include "pm2.61i.mm"

theorem evpmss
  let cD: class D
  let cP: class P
  let cS: class S
  let vd: setvar d
  let cN: class N
  assume evpmss.s: |- S = ( SymGrp ` D )
  assume evpmss.p: |- P = ( Base ` S )


  assert |- ( pmEven ` D ) C_ P

  proof
    cD
    cvv
    wcel
    #
    cD
    cevpm
    cfv
    #
    cP
    wss
    @0
    @1
    cD
    cpsgn
    cfv
    #
    ccnv
    #
    c1
    csn
    #
    cima
    #
    cP
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
    @4
    cima
    @5
    cvv
    cevpm
    @6
    cD
    wceq
    #
    @8
    @3
    @4
    @9
    @7
    @2
    @6
    cD
    cpsgn
    fveq2
    cnveqd
    imaeq1d
    vd
    df-evpm
    @3
    @4
    @2
    cD
    cpsgn
    fvex
    cnvex
    imaex
    fvmpt
    @0
    @5
    @2
    cdm
    #
    cP
    @2
    @4
    cnvimass
    @0
    @10
    cS
    @10
    cress
    co
    #
    cbs
    cfv
    #
    cP
    @0
    @2
    @11
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
    cghm
    co
    wcel
    @12
    @13
    cbs
    cfv
    #
    @2
    wf
    @10
    @12
    wceq
    cD
    cS
    @13
    @11
    @2
    cvv
    evpmss.s
    @2
    eqid
    @11
    eqid
    #
    @13
    eqid
    psgnghm
    @11
    @13
    @2
    @12
    @14
    @12
    eqid
    @14
    eqid
    ghmf
    @12
    @14
    @2
    fdm
    3syl
    @10
    cP
    @11
    cS
    @15
    evpmss.p
    ressbasss
    syl6eqss
    syl5ss
    eqsstrd
    @0
    wn
    @1
    c0
    cP
    cD
    cevpm
    fvprc
    cP
    0ss
    syl6eqss
    pm2.61i
end
