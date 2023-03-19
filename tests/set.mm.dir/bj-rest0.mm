include "c0.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wex.mm"
include "in0.mm"
include "incom.mm"
include "eqtr3i.mm"
include "0ex.mm"
include "eleq1.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spcev.mm"
include "mpan2.mm"
include "df-rex.mm"
include "sylibr.mm"
include "elrest.mm"
include "syl5ibr.mm"

theorem bj-rest0
  let cA: class A
  let cV: class V
  let cW: class W
  let cX: class X
  let vx: setvar x


  assert |- ( ( X e. V /\ A e. W ) -> ( (/) e. X -> (/) e. ( X |`t A ) ) )

  proof
    c0
    cX
    wcel
    #
    c0
    cX
    cA
    crest
    co
    wcel
    cX
    cV
    wcel
    cA
    cW
    wcel
    wa
    c0
    vx
    cv
    #
    cA
    cin
    #
    wceq
    #
    vx
    cX
    wrex
    #
    @0
    @1
    cX
    wcel
    #
    @3
    wa
    #
    vx
    wex
    #
    @4
    @0
    c0
    c0
    cA
    cin
    #
    wceq
    #
    @7
    cA
    c0
    cin
    c0
    @8
    cA
    in0
    cA
    c0
    incom
    eqtr3i
    @6
    @0
    @9
    wa
    vx
    c0
    0ex
    @1
    c0
    wceq
    #
    @5
    @0
    @3
    @9
    @1
    c0
    cX
    eleq1
    @10
    @2
    @8
    c0
    @1
    c0
    cA
    ineq1
    eqeq2d
    anbi12d
    spcev
    mpan2
    @3
    vx
    cX
    df-rex
    sylibr
    vx
    c0
    cA
    cX
    cV
    cW
    elrest
    syl5ibr
end
