include "crecs.mm"
include "wrel.mm"
include "cuni.mm"
include "cv.mm"
include "reluni.mm"
include "wcel.mm"
include "wfun.mm"
include "tfrlem4.mm"
include "funrel.mm"
include "syl.mm"
include "mprgbir.mm"
include "recsfval.mm"
include "releqi.mm"
include "mpbir.mm"

theorem tfrlem6
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let cF: class F
  let vg: setvar g
  let vz: setvar z
  let cB: class B
  let cC: class C
  let va: setvar a
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f z
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C f
  disjoint C x
  disjoint C y
  disjoint C z
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint F a
  disjoint f h
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint g h
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint F g
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint F h
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint F z
  disjoint A g
  disjoint A h
  disjoint A z
  assert |- Rel recs ( F )

  proof
    cF
    crecs
    #
    wrel
    cA
    cuni
    #
    wrel
    #
    @2
    vg
    cv
    #
    wrel
    #
    vg
    cA
    vg
    cA
    reluni
    @3
    cA
    wcel
    @3
    wfun
    @4
    vx
    vy
    cA
    vf
    vg
    cF
    tfrlem.1
    tfrlem4
    @3
    funrel
    syl
    mprgbir
    @0
    @1
    vx
    vy
    cA
    vf
    cF
    tfrlem.1
    recsfval
    releqi
    mpbir
end
