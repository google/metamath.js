include "cv.mm"
include "cpjh.mm"
include "cfv.mm"
include "cch.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "fvex.mm"
include "fvmpt.mm"

theorem hstrlem2
  let vx: setvar x
  let vu: setvar u
  let cC: class C
  let cS: class S
  assume hstrlem2.1: |- S = ( x e. CH |-> ( ( projh ` x ) ` u ) )

  disjoint C x
  disjoint u x
  assert |- ( C e. CH -> ( S ` C ) = ( ( projh ` C ) ` u ) )

  proof
    vx
    cC
    vu
    cv
    #
    vx
    cv
    #
    cpjh
    cfv
    #
    cfv
    @0
    cC
    cpjh
    cfv
    #
    cfv
    cch
    cS
    @1
    cC
    wceq
    @0
    @2
    @3
    @1
    cC
    cpjh
    fveq2
    fveq1d
    hstrlem2.1
    @0
    @3
    fvex
    fvmpt
end
