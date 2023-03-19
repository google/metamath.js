include "cvv.mm"
include "difindi.mm"

theorem indm
  let cA: class A
  let cB: class B


  assert |- ( _V \ ( A i^i B ) ) = ( ( _V \ A ) u. ( _V \ B ) )

  proof
    cvv
    cA
    cB
    difindi
end
