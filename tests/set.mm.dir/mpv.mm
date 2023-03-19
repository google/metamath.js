include "cmp.mm"
include "cmq.mm"
include "df-mp.mm"
include "cv.mm"
include "mulclnq.mm"
include "genpv.mm"

theorem mpv
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vv: setvar v
  let vu: setvar u

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint f x
  disjoint g x
  disjoint h x
  disjoint f y
  disjoint g y
  disjoint h y
  disjoint f z
  disjoint g z
  disjoint h z
  disjoint f g
  disjoint f h
  disjoint A f
  disjoint g h
  disjoint A g
  disjoint A h
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint v x
  disjoint u x
  disjoint v y
  disjoint u y
  disjoint v z
  disjoint u z
  disjoint u v
  disjoint f v
  disjoint g v
  disjoint h v
  disjoint f u
  disjoint g u
  disjoint h u
  assert |- ( ( A e. P. /\ B e. P. ) -> ( A .P. B ) = { x | E. y e. A E. z e. B x = ( y .Q z ) } )

  proof
    vf
    vg
    vh
    vu
    vv
    cA
    cB
    vx
    vy
    vz
    cmp
    cmq
    vu
    vv
    vf
    vg
    vh
    df-mp
    vg
    cv
    vh
    cv
    mulclnq
    genpv
end
