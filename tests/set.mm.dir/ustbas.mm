include "cust.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cdm.mm"
include "wrex.mm"
include "cvv.mm"
include "wfn.mm"
include "wfun.mm"
include "wb.mm"
include "ustfn.mm"
include "fnfun.mm"
include "elunirn.mm"
include "mp2b.mm"
include "ustbas2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eleq2d.mm"
include "ibi.mm"
include "rexlimivw.mm"
include "sylbi.mm"
include "elrnust.mm"
include "impbii.mm"

theorem ustbas
  let cU: class U
  let cX: class X
  let vx: setvar x
  assume ustbas.1: |- X = dom U. U


  assert |- ( U e. U. ran UnifOn <-> U e. ( UnifOn ` X ) )

  proof
    cU
    cust
    crn
    cuni
    wcel
    #
    cU
    cX
    cust
    cfv
    #
    wcel
    #
    @0
    cU
    vx
    cv
    #
    cust
    cfv
    #
    wcel
    #
    vx
    cust
    cdm
    #
    wrex
    #
    @2
    cust
    cvv
    wfn
    cust
    wfun
    @0
    @7
    wb
    ustfn
    cvv
    cust
    fnfun
    vx
    cU
    cust
    elunirn
    mp2b
    @5
    @2
    vx
    @6
    @5
    @2
    @5
    @4
    @1
    cU
    @5
    @3
    cX
    cust
    @5
    @3
    cU
    cuni
    cdm
    cX
    cU
    @3
    ustbas2
    ustbas.1
    syl6eqr
    fveq2d
    eleq2d
    ibi
    rexlimivw
    sylbi
    cU
    cX
    elrnust
    impbii
end
