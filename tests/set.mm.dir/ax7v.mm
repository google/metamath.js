include "ax-7.mm"

theorem ax7v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  assert |- ( x = y -> ( x = z -> y = z ) )

  proof
    vx
    vy
    vz
    ax-7
end
