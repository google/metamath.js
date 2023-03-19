include "cin.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "inindir.mm"
include "df-res.mm"
include "ineq12i.mm"
include "3eqtr4i.mm"

theorem resindir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i B ) |` C ) = ( ( A |` C ) i^i ( B |` C ) )

  proof
    cA
    cB
    cin
    #
    cC
    cvv
    cxp
    #
    cin
    cA
    @1
    cin
    #
    cB
    @1
    cin
    #
    cin
    @0
    cC
    cres
    cA
    cC
    cres
    #
    cB
    cC
    cres
    #
    cin
    cA
    cB
    @1
    inindir
    @0
    cC
    df-res
    @4
    @2
    @5
    @3
    cA
    cC
    df-res
    cB
    cC
    df-res
    ineq12i
    3eqtr4i
end
