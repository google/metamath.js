include "cacs.mm"
include "cfv.mm"
include "wcel.mm"
include "wss.mm"
include "cv.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "acsfiel.mm"
include "baibd.mm"

theorem acsfiel2
  let vy: setvar y
  let cC: class C
  let cS: class S
  let cF: class F
  let cX: class X
  let vc: setvar c
  let vf: setvar f
  let vs: setvar s
  let vt: setvar t
  let vz: setvar z
  let vx: setvar x
  assume isacs2.f: |- F = ( mrCls ` C )

  disjoint C y
  disjoint F y
  disjoint S y
  disjoint X y
  disjoint C c
  disjoint C f
  disjoint C s
  disjoint c f
  disjoint c s
  disjoint f s
  disjoint C t
  disjoint t y
  disjoint F f
  disjoint F s
  disjoint F t
  disjoint F z
  disjoint f t
  disjoint f y
  disjoint f z
  disjoint s t
  disjoint s y
  disjoint s z
  disjoint t z
  disjoint y z
  disjoint S s
  disjoint X c
  disjoint X f
  disjoint X s
  disjoint X x
  disjoint c x
  disjoint f x
  disjoint s x
  disjoint X t
  assert |- ( ( C e. ( ACS ` X ) /\ S C_ X ) -> ( S e. C <-> A. y e. ( ~P S i^i Fin ) ( F ` y ) C_ S ) )

  proof
    cC
    cX
    cacs
    cfv
    wcel
    cS
    cC
    wcel
    cS
    cX
    wss
    vy
    cv
    cF
    cfv
    cS
    wss
    vy
    cS
    cpw
    cfn
    cin
    wral
    vy
    cC
    cS
    cF
    cX
    isacs2.f
    acsfiel
    baibd
end
