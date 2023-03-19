include "cin.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "xpindir.mm"
include "ineq2i.mm"
include "inindi.mm"
include "eqtri.mm"
include "df-res.mm"
include "ineq12i.mm"
include "3eqtr4i.mm"

theorem resindi
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A |` ( B i^i C ) ) = ( ( A |` B ) i^i ( A |` C ) )

  proof
    cA
    cB
    cC
    cin
    #
    cvv
    cxp
    #
    cin
    #
    cA
    cB
    cvv
    cxp
    #
    cin
    #
    cA
    cC
    cvv
    cxp
    #
    cin
    #
    cin
    #
    cA
    @0
    cres
    cA
    cB
    cres
    #
    cA
    cC
    cres
    #
    cin
    @2
    cA
    @3
    @5
    cin
    #
    cin
    @7
    @1
    @10
    cA
    cB
    cC
    cvv
    xpindir
    ineq2i
    cA
    @3
    @5
    inindi
    eqtri
    cA
    @0
    df-res
    @8
    @4
    @9
    @6
    cA
    cB
    df-res
    cA
    cC
    df-res
    ineq12i
    3eqtr4i
end
