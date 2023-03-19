include "ax8v.mm"

theorem ax8v2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint y z
  assert |- ( x = y -> ( x e. z -> y e. z ) )

  proof
    vx
    vy
    vz
    ax8v
end
