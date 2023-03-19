include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "wn.mm"
include "wral.mm"
include "wi.mm"
include "disj.mm"
include "wa.mm"
include "eleq1.mm"
include "notbid.mm"
include "rspccva.mm"
include "eleq1a.mm"
include "necon3bd.mm"
include "syl5com.mm"
include "sylanb.mm"
include "3impia.mm"

theorem disjne
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x


  assert |- ( ( ( A i^i B ) = (/) /\ C e. A /\ D e. B ) -> C =/= D )

  proof
    cA
    cB
    cin
    c0
    wceq
    #
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    cC
    cD
    wne
    #
    @0
    vx
    cv
    #
    cB
    wcel
    #
    wn
    #
    vx
    cA
    wral
    #
    @1
    @2
    @3
    wi
    vx
    cA
    cB
    disj
    @7
    @1
    wa
    cC
    cB
    wcel
    #
    wn
    #
    @2
    @3
    @6
    @9
    vx
    cC
    cA
    @4
    cC
    wceq
    @5
    @8
    @4
    cC
    cB
    eleq1
    notbid
    rspccva
    @2
    @8
    cC
    cD
    cD
    cB
    cC
    eleq1a
    necon3bd
    syl5com
    sylanb
    3impia
end
