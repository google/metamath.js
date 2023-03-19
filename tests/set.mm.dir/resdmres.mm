include "cres.mm"
include "cdm.mm"
include "ccnv.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "in12.mm"
include "df-res.mm"
include "resdm2.mm"
include "eqtr3i.mm"
include "ineq2i.mm"
include "incom.mm"
include "3eqtri.mm"
include "dmres.mm"
include "xpeq1i.mm"
include "xpindir.mm"
include "eqtri.mm"
include "3eqtr4i.mm"
include "rescnvcnv.mm"

theorem resdmres
  let cA: class A
  let cB: class B


  assert |- ( A |` dom ( A |` B ) ) = ( A |` B )

  proof
    cA
    cA
    cB
    cres
    #
    cdm
    #
    cres
    #
    cA
    ccnv
    ccnv
    #
    cB
    cres
    #
    @0
    cA
    cB
    cvv
    cxp
    #
    cA
    cdm
    #
    cvv
    cxp
    #
    cin
    #
    cin
    #
    @3
    @5
    cin
    #
    @2
    @4
    @9
    @5
    cA
    @7
    cin
    #
    cin
    @5
    @3
    cin
    @10
    cA
    @5
    @7
    in12
    @11
    @3
    @5
    cA
    @6
    cres
    @11
    @3
    cA
    @6
    df-res
    cA
    resdm2
    eqtr3i
    ineq2i
    @5
    @3
    incom
    3eqtri
    @2
    cA
    @1
    cvv
    cxp
    #
    cin
    @9
    cA
    @1
    df-res
    @12
    @8
    cA
    @12
    cB
    @6
    cin
    #
    cvv
    cxp
    @8
    @1
    @13
    cvv
    cA
    cB
    dmres
    xpeq1i
    cB
    @6
    cvv
    xpindir
    eqtri
    ineq2i
    eqtri
    @3
    cB
    df-res
    3eqtr4i
    cA
    cB
    rescnvcnv
    eqtri
end
