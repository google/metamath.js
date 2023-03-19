include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "grpoidinv2.mm"
include "simplr.mm"
include "syl.mm"

theorem grporid
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  assume grpoidval.1: |- X = ran G
  assume grpoidval.2: |- U = ( GId ` G )


  assert |- ( ( G e. GrpOp /\ A e. X ) -> ( A G U ) = A )

  proof
    cG
    cgr
    wcel
    cA
    cX
    wcel
    wa
    cU
    cA
    cG
    co
    cA
    wceq
    #
    cA
    cU
    cG
    co
    cA
    wceq
    #
    wa
    vx
    cv
    #
    cA
    cG
    co
    cU
    wceq
    cA
    @2
    cG
    co
    cU
    wceq
    wa
    vx
    cX
    wrex
    #
    wa
    @1
    vx
    cA
    cU
    cG
    cX
    grpoidval.1
    grpoidval.2
    grpoidinv2
    @0
    @1
    @3
    simplr
    syl
end
