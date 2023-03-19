include "cv.mm"
include "wcel.mm"
include "wfn.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "wfun.mm"
include "tfrlem3.mm"
include "abeq2i.mm"
include "fnfun.mm"
include "adantr.mm"
include "rexlimivw.mm"
include "sylbi.mm"

theorem tfrlem4
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let vz: setvar z
  let cB: class B
  let cC: class C
  let va: setvar a
  let vh: setvar h
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  assume tfrlem.1: |- A = { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( F ` ( f |` y ) ) ) }

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint g x
  disjoint g y
  disjoint x y
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint A g
  disjoint f z
  disjoint B f
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
  disjoint A h
  disjoint A z
  assert |- ( g e. A -> Fun g )

  proof
    vg
    cv
    #
    cA
    wcel
    @0
    vz
    cv
    #
    wfn
    #
    vw
    cv
    #
    @0
    cfv
    @0
    @3
    cres
    cF
    cfv
    wceq
    vw
    @1
    wral
    #
    wa
    #
    vz
    con0
    wrex
    #
    @0
    wfun
    #
    @6
    vg
    cA
    vx
    vy
    vz
    vw
    cA
    vf
    vg
    cF
    tfrlem.1
    tfrlem3
    abeq2i
    @5
    @7
    vz
    con0
    @2
    @7
    @4
    @1
    @0
    fnfun
    adantr
    rexlimivw
    sylbi
end
