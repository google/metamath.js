include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "cfi.mm"
include "cfv.mm"
include "fveq2.mm"
include "fi0.mm"
include "syl6eq.mm"
include "wss.mm"
include "ssfii.mm"
include "sseq0.mm"
include "sylan.mm"
include "ex.mm"
include "impbid2.mm"

theorem fieq0
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> ( A = (/) <-> ( fi ` A ) = (/) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    c0
    wceq
    #
    cA
    cfi
    cfv
    #
    c0
    wceq
    #
    @1
    @2
    c0
    cfi
    cfv
    c0
    cA
    c0
    cfi
    fveq2
    fi0
    syl6eq
    @0
    @3
    @1
    @0
    cA
    @2
    wss
    @3
    @1
    cA
    cV
    ssfii
    cA
    @2
    sseq0
    sylan
    ex
    impbid2
end
