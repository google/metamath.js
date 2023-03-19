include "ax-8.mm"

theorem ax8v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  assert |- ( x = y -> ( x e. z -> y e. z ) )

  proof
    vx
    vy
    vz
    ax-8
end
