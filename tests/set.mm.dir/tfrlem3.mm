include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "vex.mm"
include "tfrlem3a.mm"
include "abbi2i.mm"

theorem tfrlem3
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cG: class G
  assume tfrlem3.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }

  disjoint A g
  disjoint f g
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint F f
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint F g
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint G f
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  assert |- A = { g | E. z e. On ( g Fn z /\ A. w e. z ( g ` w ) = ( F ` ( g |` w ) ) ) }

  proof
    vg
    cv
    #
    vz
    cv
    #
    wfn
    vw
    cv
    #
    @0
    cfv
    @0
    @2
    cres
    cF
    cfv
    wceq
    vw
    @1
    wral
    wa
    vz
    con0
    wrex
    vg
    cA
    vx
    vy
    vz
    vw
    cA
    vf
    cF
    @0
    tfrlem3.1
    vg
    vex
    tfrlem3a
    abbi2i
end
