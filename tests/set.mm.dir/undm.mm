include "cvv.mm"
include "difundi.mm"

theorem undm
  let cA: class A
  let cB: class B


  assert |- ( _V \ ( A u. B ) ) = ( ( _V \ A ) i^i ( _V \ B ) )

  proof
    cvv
    cA
    cB
    difundi
end
