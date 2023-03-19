include "cin.mm"
include "in12.mm"
include "ineq2i.mm"
include "inass.mm"
include "3eqtr4i.mm"

theorem in4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A i^i B ) i^i ( C i^i D ) ) = ( ( A i^i C ) i^i ( B i^i D ) )

  proof
    cA
    cB
    cC
    cD
    cin
    #
    cin
    #
    cin
    cA
    cC
    cB
    cD
    cin
    #
    cin
    #
    cin
    cA
    cB
    cin
    @0
    cin
    cA
    cC
    cin
    @2
    cin
    @1
    @3
    cA
    cB
    cC
    cD
    in12
    ineq2i
    cA
    cB
    @0
    inass
    cA
    cC
    @2
    inass
    3eqtr4i
end
