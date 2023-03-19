include "cvv.mm"
include "difcom.mm"

theorem conss1
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( _V \ A ) C_ B <-> ( _V \ B ) C_ A )

  proof
    cvv
    cA
    cB
    difcom
end
