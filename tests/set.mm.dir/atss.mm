include "cat.mm"
include "wcel.mm"
include "cch.mm"
include "c0h.mm"
include "wne.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "elat2.mm"
include "sseq1.mm"
include "eqeq1.mm"
include "orbi12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "adantld.mm"
include "imp.mm"
include "sylan2b.mm"

theorem atss
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. CH /\ B e. HAtoms ) -> ( A C_ B -> ( A = B \/ A = 0H ) ) )

  proof
    cB
    cat
    wcel
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cB
    c0h
    wne
    #
    vx
    cv
    #
    cB
    wss
    #
    @3
    cB
    wceq
    #
    @3
    c0h
    wceq
    #
    wo
    #
    wi
    #
    vx
    cch
    wral
    #
    wa
    #
    wa
    #
    cA
    cB
    wss
    #
    cA
    cB
    wceq
    #
    cA
    c0h
    wceq
    #
    wo
    #
    wi
    #
    vx
    cB
    elat2
    @0
    @11
    @16
    @0
    @10
    @16
    @1
    @0
    @9
    @16
    @2
    @8
    @16
    vx
    cA
    cch
    @3
    cA
    wceq
    #
    @4
    @12
    @7
    @15
    @3
    cA
    cB
    sseq1
    @17
    @5
    @13
    @6
    @14
    @3
    cA
    cB
    eqeq1
    @3
    cA
    c0h
    eqeq1
    orbi12d
    imbi12d
    rspcv
    adantld
    adantld
    imp
    sylan2b
end
