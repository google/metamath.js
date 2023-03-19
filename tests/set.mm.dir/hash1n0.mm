include "wcel.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "csn.mm"
include "wex.mm"
include "hash1snb.mm"
include "id.mm"
include "vex.mm"
include "snnz.mm"
include "a1i.mm"
include "eqnetrd.mm"
include "exlimiv.mm"
include "syl6bi.mm"
include "imp.mm"

theorem hash1n0
  let cA: class A
  let cV: class V
  let va: setvar a


  assert |- ( ( A e. V /\ ( # ` A ) = 1 ) -> A =/= (/) )

  proof
    cA
    cV
    wcel
    #
    cA
    chash
    cfv
    c1
    wceq
    #
    cA
    c0
    wne
    #
    @0
    @1
    cA
    va
    cv
    #
    csn
    #
    wceq
    #
    va
    wex
    @2
    cA
    cV
    va
    hash1snb
    @5
    @2
    va
    @5
    cA
    @4
    c0
    @5
    id
    @4
    c0
    wne
    @5
    @3
    va
    vex
    snnz
    a1i
    eqnetrd
    exlimiv
    syl6bi
    imp
end
