include "wf.mm"
include "cv.mm"
include "wfo.mm"
include "wss.mm"
include "wa.mm"
include "wex.mm"
include "crn.mm"
include "wfn.mm"
include "df-f.mm"
include "dffn4.mm"
include "anbi1i.mm"
include "bitri.mm"
include "rnex.mm"
include "wceq.mm"
include "foeq3.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "spcev.mm"
include "sylbi.mm"
include "fof.mm"
include "fss.mm"
include "sylan.mm"
include "exlimiv.mm"
include "impbii.mm"

theorem ffoss
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  assume f11o.1: |- F e. _V

  disjoint F x
  disjoint A x
  disjoint B x
  assert |- ( F : A --> B <-> E. x ( F : A -onto-> x /\ x C_ B ) )

  proof
    cA
    cB
    cF
    wf
    #
    cA
    vx
    cv
    #
    cF
    wfo
    #
    @1
    cB
    wss
    #
    wa
    #
    vx
    wex
    #
    @0
    cA
    cF
    crn
    #
    cF
    wfo
    #
    @6
    cB
    wss
    #
    wa
    #
    @5
    @0
    cF
    cA
    wfn
    #
    @8
    wa
    @9
    cA
    cB
    cF
    df-f
    @10
    @7
    @8
    cA
    cF
    dffn4
    anbi1i
    bitri
    @4
    @9
    vx
    @6
    cF
    f11o.1
    rnex
    @1
    @6
    wceq
    @2
    @7
    @3
    @8
    @1
    @6
    cA
    cF
    foeq3
    @1
    @6
    cB
    sseq1
    anbi12d
    spcev
    sylbi
    @4
    @0
    vx
    @2
    cA
    @1
    cF
    wf
    @3
    @0
    cA
    @1
    cF
    fof
    cA
    @1
    cB
    cF
    fss
    sylan
    exlimiv
    impbii
end
