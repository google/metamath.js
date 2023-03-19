include "cin.mm"
include "cvv.mm"
include "cxp.mm"
include "cres.mm"
include "inass.mm"
include "df-res.mm"
include "ineq2i.mm"
include "3eqtr4ri.mm"

theorem inres
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A i^i ( B |` C ) ) = ( ( A i^i B ) |` C )

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
    cB
    @1
    cin
    #
    cin
    @0
    cC
    cres
    cA
    cB
    cC
    cres
    #
    cin
    cA
    cB
    @1
    inass
    @0
    cC
    df-res
    @3
    @2
    cA
    cB
    cC
    df-res
    ineq2i
    3eqtr4ri
end
