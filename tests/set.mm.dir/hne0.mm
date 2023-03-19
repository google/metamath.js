include "chil.mm"
include "helch.mm"
include "chne0i.mm"

theorem hne0
  let vx: setvar x


  assert |- ( ~H =/= 0H <-> E. x e. ~H x =/= 0h )

  proof
    vx
    chil
    helch
    chne0i
end
