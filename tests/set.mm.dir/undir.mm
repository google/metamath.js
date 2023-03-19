include "cin.mm"
include "cun.mm"
include "undi.mm"
include "uncom.mm"
include "ineq12i.mm"
include "3eqtr4i.mm"

theorem undir
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A i^i B ) u. C ) = ( ( A u. C ) i^i ( B u. C ) )

  proof
    cC
    cA
    cB
    cin
    #
    cun
    cC
    cA
    cun
    #
    cC
    cB
    cun
    #
    cin
    @0
    cC
    cun
    cA
    cC
    cun
    #
    cB
    cC
    cun
    #
    cin
    cC
    cA
    cB
    undi
    @0
    cC
    uncom
    @3
    @1
    @4
    @2
    cA
    cC
    uncom
    cB
    cC
    uncom
    ineq12i
    3eqtr4i
end
