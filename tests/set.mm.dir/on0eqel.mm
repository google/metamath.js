include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "wo.mm"
include "wss.mm"
include "0ss.mm"
include "wb.mm"
include "0elon.mm"
include "onsseleq.mm"
include "mpan.mm"
include "mpbii.mm"
include "eqcom.mm"
include "orbi2i.mm"
include "orcom.mm"
include "bitri.mm"
include "sylib.mm"

theorem on0eqel
  let cA: class A


  assert |- ( A e. On -> ( A = (/) \/ (/) e. A ) )

  proof
    cA
    con0
    wcel
    #
    c0
    cA
    wcel
    #
    c0
    cA
    wceq
    #
    wo
    #
    cA
    c0
    wceq
    #
    @1
    wo
    #
    @0
    c0
    cA
    wss
    #
    @3
    cA
    0ss
    c0
    con0
    wcel
    @0
    @6
    @3
    wb
    0elon
    c0
    cA
    onsseleq
    mpan
    mpbii
    @3
    @1
    @4
    wo
    @5
    @2
    @4
    @1
    c0
    cA
    eqcom
    orbi2i
    @1
    @4
    orcom
    bitri
    sylib
end
