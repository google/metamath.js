include "wcel.mm"
include "ctc.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "wi.mm"
include "tcid.mm"
include "sseq0.mm"
include "ex.mm"
include "syl.mm"
include "fveq2.mm"
include "tc0.mm"
include "syl6eq.mm"
include "impbid1.mm"

theorem tc00
  let cA: class A
  let cV: class V


  assert |- ( A e. V -> ( ( TC ` A ) = (/) <-> A = (/) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    ctc
    cfv
    #
    c0
    wceq
    #
    cA
    c0
    wceq
    #
    @0
    cA
    @1
    wss
    #
    @2
    @3
    wi
    cA
    cV
    tcid
    @4
    @2
    @3
    cA
    @1
    sseq0
    ex
    syl
    @3
    @1
    c0
    ctc
    cfv
    c0
    cA
    c0
    ctc
    fveq2
    tc0
    syl6eq
    impbid1
end
