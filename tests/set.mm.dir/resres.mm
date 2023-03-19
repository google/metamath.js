include "cres.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "df-res.mm"
include "ineq1i.mm"
include "xpindir.mm"
include "ineq2i.mm"
include "inass.mm"
include "3eqtr4ri.mm"
include "3eqtri.mm"

theorem resres
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A |` B ) |` C ) = ( A |` ( B i^i C ) )

  proof
    cA
    cB
    cres
    #
    cC
    cres
    @0
    cC
    cvv
    cxp
    #
    cin
    cA
    cB
    cvv
    cxp
    #
    cin
    #
    @1
    cin
    #
    cA
    cB
    cC
    cin
    #
    cres
    #
    @0
    cC
    df-res
    @0
    @3
    @1
    cA
    cB
    df-res
    ineq1i
    cA
    @5
    cvv
    cxp
    #
    cin
    cA
    @2
    @1
    cin
    #
    cin
    @6
    @4
    @7
    @8
    cA
    cB
    cC
    cvv
    xpindir
    ineq2i
    cA
    @5
    df-res
    cA
    @2
    @1
    inass
    3eqtr4ri
    3eqtri
end
