include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "wrex.mm"
include "crn.mm"
include "cuni.mm"
include "elfvdm.mm"
include "wceq.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "rspcev.mm"
include "mpancom.mm"
include "cvv.mm"
include "wfn.mm"
include "wfun.mm"
include "wb.mm"
include "ustfn.mm"
include "fnfun.mm"
include "elunirn.mm"
include "mp2b.mm"
include "sylibr.mm"

theorem elrnust
  let cU: class U
  let cX: class X
  let vx: setvar x


  assert |- ( U e. ( UnifOn ` X ) -> U e. U. ran UnifOn )

  proof
    cU
    cX
    cust
    cfv
    #
    wcel
    #
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
    cU
    cust
    crn
    cuni
    wcel
    #
    cX
    @5
    wcel
    @1
    @6
    cU
    cX
    cust
    elfvdm
    @4
    @1
    vx
    cX
    @5
    @2
    cX
    wceq
    @3
    @0
    cU
    @2
    cX
    cust
    fveq2
    eleq2d
    rspcev
    mpancom
    cust
    cvv
    wfn
    cust
    wfun
    @7
    @6
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
    sylibr
end
