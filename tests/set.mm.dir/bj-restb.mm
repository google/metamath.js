include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "crest.mm"
include "co.mm"
include "cv.mm"
include "cin.mm"
include "wceq.mm"
include "wrex.mm"
include "wex.mm"
include "id.mm"
include "ssid.mm"
include "a1i.mm"
include "ssind.mm"
include "inss2.mm"
include "eqssd.mm"
include "wi.mm"
include "eleq1.mm"
include "ineq1.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "expd.mm"
include "pm2.43i.mm"
include "mpan9.mm"
include "df-rex.mm"
include "sylibr.mm"
include "adantl.mm"
include "cvv.mm"
include "wb.mm"
include "ssexg.mm"
include "elrest.mm"
include "sylan2.mm"
include "mpbird.mm"
include "ex.mm"

theorem bj-restb
  let cA: class A
  let cB: class B
  let cV: class V
  let cX: class X
  let vy: setvar y


  assert |- ( X e. V -> ( ( A C_ B /\ B e. X ) -> A e. ( X |`t A ) ) )

  proof
    cX
    cV
    wcel
    #
    cA
    cB
    wss
    #
    cB
    cX
    wcel
    #
    wa
    #
    cA
    cX
    cA
    crest
    co
    wcel
    #
    @0
    @3
    wa
    @4
    cA
    vy
    cv
    #
    cA
    cin
    #
    wceq
    #
    vy
    cX
    wrex
    #
    @3
    @8
    @0
    @3
    @5
    cX
    wcel
    #
    @7
    wa
    #
    vy
    wex
    #
    @8
    @1
    cA
    cB
    cA
    cin
    #
    wceq
    #
    @2
    @11
    @1
    cA
    @12
    @1
    cA
    cB
    cA
    @1
    id
    cA
    cA
    wss
    @1
    cA
    ssid
    a1i
    ssind
    @12
    cA
    wss
    @1
    cB
    cA
    inss2
    a1i
    eqssd
    @2
    @13
    @11
    wi
    @2
    @2
    @13
    @11
    @10
    @2
    @13
    wa
    vy
    cB
    cX
    @5
    cB
    wceq
    #
    @9
    @2
    @7
    @13
    @5
    cB
    cX
    eleq1
    @14
    @6
    @12
    cA
    @5
    cB
    cA
    ineq1
    eqeq2d
    anbi12d
    spcegv
    expd
    pm2.43i
    mpan9
    @7
    vy
    cX
    df-rex
    sylibr
    adantl
    @3
    @0
    cA
    cvv
    wcel
    @4
    @8
    wb
    cA
    cB
    cX
    ssexg
    vy
    cA
    cA
    cX
    cV
    cvv
    elrest
    sylan2
    mpbird
    ex
end
