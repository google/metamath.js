include "cv.mm"
include "csuc.mm"
include "wceq.mm"
include "wa.mm"
include "eqtr2.mm"
include "suc11reg.mm"
include "sylib.mm"

theorem bnj551
  let vi: setvar i
  let vm: setvar m
  let vp: setvar p


  assert |- ( ( m = suc p /\ m = suc i ) -> p = i )

  proof
    vm
    cv
    #
    vp
    cv
    #
    csuc
    #
    wceq
    @0
    vi
    cv
    #
    csuc
    #
    wceq
    wa
    @2
    @4
    wceq
    @1
    @3
    wceq
    @0
    @2
    @4
    eqtr2
    @1
    @3
    suc11reg
    sylib
end
