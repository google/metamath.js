include "wceq.mm"
include "csymdif.mm"
include "symdifeq1.mm"
include "symdifcom.mm"
include "3eqtr4g.mm"

theorem symdifeq2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( A = B -> ( C /_\ A ) = ( C /_\ B ) )

  proof
    cA
    cB
    wceq
    cA
    cC
    csymdif
    cB
    cC
    csymdif
    cC
    cA
    csymdif
    cC
    cB
    csymdif
    cA
    cB
    cC
    symdifeq1
    cC
    cA
    symdifcom
    cC
    cB
    symdifcom
    3eqtr4g
end
