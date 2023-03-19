include "ax7v.mm"

theorem ax7v2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z

  disjoint x y
  disjoint y z
  assert |- ( x = y -> ( x = z -> y = z ) )

  proof
    vx
    vy
    vz
    ax7v
end
