include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "w3a.mm"
include "cref.mm"
include "wbr.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "eqcom.mm"
include "biimpi.mm"
include "3ad2ant3.mm"
include "wa.mm"
include "ssel2.mm"
include "3ad2antl2.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "sylancl.mm"
include "ralrimiva.mm"
include "wb.mm"
include "isref.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem ssref
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume ssref.1: |- X = U. A
  assume ssref.2: |- Y = U. B


  assert |- ( ( A e. C /\ A C_ B /\ X = Y ) -> A Ref B )

  proof
    cA
    cC
    wcel
    #
    cA
    cB
    wss
    #
    cX
    cY
    wceq
    #
    w3a
    #
    cA
    cB
    cref
    wbr
    #
    cY
    cX
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cB
    wrex
    #
    vx
    cA
    wral
    #
    @2
    @0
    @5
    @1
    @2
    @5
    cX
    cY
    eqcom
    biimpi
    3ad2ant3
    @3
    @9
    vx
    cA
    @3
    @6
    cA
    wcel
    #
    wa
    @6
    cB
    wcel
    #
    @6
    @6
    wss
    #
    @9
    @1
    @0
    @11
    @12
    @2
    cA
    cB
    @6
    ssel2
    3ad2antl2
    @6
    ssid
    @8
    @13
    vy
    @6
    cB
    @7
    @6
    @6
    sseq2
    rspcev
    sylancl
    ralrimiva
    @0
    @1
    @4
    @5
    @10
    wa
    wb
    @2
    vx
    vy
    cA
    cB
    cC
    cX
    cY
    ssref.1
    ssref.2
    isref
    3ad2ant1
    mpbir2and
end
