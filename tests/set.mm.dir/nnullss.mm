include "c0.mm"
include "wne.mm"
include "cv.mm"
include "wcel.mm"
include "wex.mm"
include "wss.mm"
include "wa.mm"
include "n0.mm"
include "csn.mm"
include "vex.mm"
include "snss.mm"
include "snnz.mm"
include "snex.mm"
include "wceq.mm"
include "sseq1.mm"
include "neeq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "mpan2.mm"
include "sylbi.mm"
include "exlimiv.mm"

theorem nnullss
  let vx: setvar x
  let cA: class A
  let vy: setvar y

  disjoint A x
  disjoint x y
  disjoint A y
  assert |- ( A =/= (/) -> E. x ( x C_ A /\ x =/= (/) ) )

  proof
    cA
    c0
    wne
    vy
    cv
    #
    cA
    wcel
    #
    vy
    wex
    vx
    cv
    #
    cA
    wss
    #
    @2
    c0
    wne
    #
    wa
    #
    vx
    wex
    #
    vy
    cA
    n0
    @1
    @6
    vy
    @1
    @0
    csn
    #
    cA
    wss
    #
    @6
    @0
    cA
    vy
    vex
    #
    snss
    @8
    @7
    c0
    wne
    #
    @6
    @0
    @9
    snnz
    @5
    @8
    @10
    wa
    vx
    @7
    @0
    snex
    @2
    @7
    wceq
    @3
    @8
    @4
    @10
    @2
    @7
    cA
    sseq1
    @2
    @7
    c0
    neeq1
    anbi12d
    spcev
    mpan2
    sylbi
    exlimiv
    sylbi
end
