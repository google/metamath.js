include "wcel.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wn.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wrex.mm"
include "cima.mm"
include "wo.mm"
include "fvbr0.mm"
include "orcom.mm"
include "mpbi.mm"
include "ori.mm"
include "breq1.mm"
include "rspcev.mm"
include "sylan2.mm"
include "fvex.mm"
include "elima.mm"
include "sylibr.mm"

theorem eliman0
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x


  assert |- ( ( A e. B /\ -. ( F ` A ) = (/) ) -> ( F ` A ) e. ( F " B ) )

  proof
    cA
    cB
    wcel
    #
    cA
    cF
    cfv
    #
    c0
    wceq
    #
    wn
    #
    wa
    vx
    cv
    #
    @1
    cF
    wbr
    #
    vx
    cB
    wrex
    #
    @1
    cF
    cB
    cima
    wcel
    @3
    @0
    cA
    @1
    cF
    wbr
    #
    @6
    @2
    @7
    @7
    @2
    wo
    @2
    @7
    wo
    cF
    cA
    fvbr0
    @7
    @2
    orcom
    mpbi
    ori
    @5
    @7
    vx
    cA
    cB
    @4
    cA
    @1
    cF
    breq1
    rspcev
    sylan2
    vx
    @1
    cF
    cB
    cA
    cF
    fvex
    elima
    sylibr
end
