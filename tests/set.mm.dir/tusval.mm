include "cust.mm"
include "cfv.mm"
include "wcel.mm"
include "cnx.mm"
include "cbs.mm"
include "cv.mm"
include "cuni.mm"
include "cdm.mm"
include "cop.mm"
include "cunif.mm"
include "cpr.mm"
include "cts.mm"
include "cutop.mm"
include "csts.mm"
include "co.mm"
include "crn.mm"
include "ctus.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-tus.mm"
include "a1i.mm"
include "wa.mm"
include "simpr.mm"
include "unieqd.mm"
include "dmeqd.mm"
include "opeq2d.mm"
include "preq12d.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "elrnust.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem tusval
  let cU: class U
  let cX: class X
  let vu: setvar u


  assert |- ( U e. ( UnifOn ` X ) -> ( toUnifSp ` U ) = ( { <. ( Base ` ndx ) , dom U. U >. , <. ( UnifSet ` ndx ) , U >. } sSet <. ( TopSet ` ndx ) , ( unifTop ` U ) >. ) )

  proof
    cU
    cX
    cust
    cfv
    wcel
    #
    vu
    cU
    cnx
    cbs
    cfv
    #
    vu
    cv
    #
    cuni
    #
    cdm
    #
    cop
    #
    cnx
    cunif
    cfv
    #
    @2
    cop
    #
    cpr
    #
    cnx
    cts
    cfv
    #
    @2
    cutop
    cfv
    #
    cop
    #
    csts
    co
    #
    @1
    cU
    cuni
    #
    cdm
    #
    cop
    #
    @6
    cU
    cop
    #
    cpr
    #
    @9
    cU
    cutop
    cfv
    #
    cop
    #
    csts
    co
    cust
    crn
    cuni
    #
    ctus
    cvv
    ctus
    vu
    @20
    @12
    cmpt
    wceq
    @0
    vu
    df-tus
    a1i
    @0
    @2
    cU
    wceq
    #
    wa
    #
    @8
    @17
    @11
    @19
    csts
    @22
    @5
    @15
    @7
    @16
    @22
    @4
    @14
    @1
    @22
    @3
    @13
    @22
    @2
    cU
    @0
    @21
    simpr
    #
    unieqd
    dmeqd
    opeq2d
    @22
    @2
    cU
    @6
    @23
    opeq2d
    preq12d
    @22
    @10
    @18
    @9
    @22
    @2
    cU
    cutop
    @23
    fveq2d
    opeq2d
    oveq12d
    cU
    cX
    elrnust
    @0
    @17
    @19
    csts
    ovexd
    fvmptd
end
