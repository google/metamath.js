include "chil.mm"
include "helsh.mm"
include "norm1exi.mm"

theorem norm1hex
  let vx: setvar x
  let vy: setvar y


  assert |- ( E. x e. ~H x =/= 0h <-> E. y e. ~H ( normh ` y ) = 1 )

  proof
    vx
    vy
    chil
    helsh
    norm1exi
end
