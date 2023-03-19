include "cgr.mm"
include "wcel.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wa.mm"
include "wral.mm"
include "c0.mm"
include "wne.mm"
include "grpolidinv.mm"
include "rexn0.mm"
include "syl.mm"

theorem grpon0
  let cG: class G
  let cX: class X
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let vu: setvar u
  let cU: class U
  assume grpfo.1: |- X = ran G


  assert |- ( G e. GrpOp -> X =/= (/) )

  proof
    cG
    cgr
    wcel
    vu
    cv
    #
    vx
    cv
    #
    cG
    co
    @1
    wceq
    vy
    cv
    @1
    cG
    co
    @0
    wceq
    vy
    cX
    wrex
    wa
    vx
    cX
    wral
    #
    vu
    cX
    wrex
    cX
    c0
    wne
    vx
    vy
    vu
    cG
    cX
    grpfo.1
    grpolidinv
    @2
    vu
    cX
    rexn0
    syl
end
