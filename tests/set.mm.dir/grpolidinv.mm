include "cgr.mm"
include "wcel.mm"
include "cxp.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "w3a.mm"
include "isgrpo.mm"
include "ibi.mm"
include "simp3d.mm"

theorem grpolidinv
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let cG: class G
  let cX: class X
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  assume grpfo.1: |- X = ran G

  disjoint x y
  disjoint u x
  disjoint u y
  disjoint G u
  disjoint G x
  disjoint G y
  disjoint X u
  disjoint X x
  disjoint X y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint u w
  disjoint u z
  disjoint G w
  disjoint G z
  disjoint X w
  disjoint X z
  disjoint U y
  assert |- ( G e. GrpOp -> E. u e. X A. x e. X ( ( u G x ) = x /\ E. y e. X ( y G x ) = u ) )

  proof
    cG
    cgr
    wcel
    #
    cX
    cX
    cxp
    cX
    cG
    wf
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    vz
    cv
    #
    cG
    co
    @2
    @3
    @4
    cG
    co
    cG
    co
    wceq
    vz
    cX
    wral
    vy
    cX
    wral
    vx
    cX
    wral
    #
    vu
    cv
    #
    @2
    cG
    co
    @2
    wceq
    @3
    @2
    cG
    co
    @6
    wceq
    vy
    cX
    wrex
    wa
    vx
    cX
    wral
    vu
    cX
    wrex
    #
    @0
    @1
    @5
    @7
    w3a
    vx
    vy
    vz
    vu
    cgr
    cG
    cX
    grpfo.1
    isgrpo
    ibi
    simp3d
end
