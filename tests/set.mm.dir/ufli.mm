include "cufl.mm"
include "wcel.mm"
include "cv.mm"
include "wss.mm"
include "cufil.mm"
include "cfv.mm"
include "wrex.mm"
include "cfil.mm"
include "wral.mm"
include "isufl.mm"
include "ibi.mm"
include "wceq.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "sylan.mm"

theorem ufli
  let vf: setvar f
  let cF: class F
  let cX: class X
  let vg: setvar g
  let vu: setvar u
  let vx: setvar x
  let cY: class Y

  disjoint F f
  disjoint X f
  disjoint f g
  disjoint F g
  disjoint f u
  disjoint f x
  disjoint g u
  disjoint g x
  disjoint X g
  disjoint u x
  disjoint X u
  disjoint X x
  disjoint Y f
  disjoint Y g
  disjoint Y u
  assert |- ( ( X e. UFL /\ F e. ( Fil ` X ) ) -> E. f e. ( UFil ` X ) F C_ f )

  proof
    cX
    cufl
    wcel
    #
    vg
    cv
    #
    vf
    cv
    #
    wss
    #
    vf
    cX
    cufil
    cfv
    #
    wrex
    #
    vg
    cX
    cfil
    cfv
    #
    wral
    #
    cF
    @6
    wcel
    cF
    @2
    wss
    #
    vf
    @4
    wrex
    #
    @0
    @7
    vg
    vf
    cufl
    cX
    isufl
    ibi
    @5
    @9
    vg
    cF
    @6
    @1
    cF
    wceq
    @3
    @8
    vf
    @4
    @1
    cF
    @2
    sseq1
    rexbidv
    rspccva
    sylan
end
