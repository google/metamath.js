include "cotrg.mm"

theorem cotr
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cR: class R

  disjoint x y
  disjoint x z
  disjoint R x
  disjoint y z
  disjoint R y
  disjoint R z
  assert |- ( ( R o. R ) C_ R <-> A. x A. y A. z ( ( x R y /\ y R z ) -> x R z ) )

  proof
    vx
    vy
    vz
    cR
    cR
    cR
    cotrg
end
