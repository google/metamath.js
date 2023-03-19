include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "cun.mm"
include "uneq12.mm"
include "un0.mm"
include "syl6eq.mm"
include "wss.mm"
include "ssun1.mm"
include "sseq2.mm"
include "mpbii.mm"
include "ss0b.mm"
include "sylib.mm"
include "ssun2.mm"
include "jca.mm"
include "impbii.mm"

theorem un00
  let cA: class A
  let cB: class B


  assert |- ( ( A = (/) /\ B = (/) ) <-> ( A u. B ) = (/) )

  proof
    cA
    c0
    wceq
    #
    cB
    c0
    wceq
    #
    wa
    #
    cA
    cB
    cun
    #
    c0
    wceq
    #
    @2
    @3
    c0
    c0
    cun
    c0
    cA
    c0
    cB
    c0
    uneq12
    c0
    un0
    syl6eq
    @4
    @0
    @1
    @4
    cA
    c0
    wss
    #
    @0
    @4
    cA
    @3
    wss
    @5
    cA
    cB
    ssun1
    @3
    c0
    cA
    sseq2
    mpbii
    cA
    ss0b
    sylib
    @4
    cB
    c0
    wss
    #
    @1
    @4
    cB
    @3
    wss
    @6
    cB
    cA
    ssun2
    @3
    c0
    cB
    sseq2
    mpbii
    cB
    ss0b
    sylib
    jca
    impbii
end
