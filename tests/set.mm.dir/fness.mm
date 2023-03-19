include "wcel.mm"
include "wss.mm"
include "wceq.mm"
include "w3a.mm"
include "cfne.mm"
include "wbr.mm"
include "wel.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "wral.mm"
include "simp3.mm"
include "ssel2.mm"
include "3adant3.mm"
include "ssid.mm"
include "jctir.mm"
include "elequ2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "3expib.mm"
include "ralrimivv.mm"
include "3ad2ant2.mm"
include "wb.mm"
include "isfne2.mm"
include "3ad2ant1.mm"
include "mpbir2and.mm"

theorem fness
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume fness.1: |- X = U. A
  assume fness.2: |- Y = U. B


  assert |- ( ( B e. C /\ A C_ B /\ X = Y ) -> A Fne B )

  proof
    cB
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
    cA
    cB
    cfne
    wbr
    #
    @2
    vy
    vz
    wel
    #
    vz
    cv
    #
    vx
    cv
    #
    wss
    #
    wa
    #
    vz
    cB
    wrex
    #
    vy
    @6
    wral
    vx
    cA
    wral
    #
    @0
    @1
    @2
    simp3
    @1
    @0
    @10
    @2
    @1
    @9
    vx
    vy
    cA
    @6
    @1
    @6
    cA
    wcel
    #
    vy
    vx
    wel
    #
    @9
    @1
    @11
    @12
    w3a
    #
    @6
    cB
    wcel
    #
    @12
    @6
    @6
    wss
    #
    wa
    #
    @9
    @1
    @11
    @14
    @12
    cA
    cB
    @6
    ssel2
    3adant3
    @13
    @12
    @15
    @1
    @11
    @12
    simp3
    @6
    ssid
    jctir
    @8
    @16
    vz
    @6
    cB
    @5
    @6
    wceq
    @4
    @12
    @7
    @15
    vz
    vx
    vy
    elequ2
    @5
    @6
    @6
    sseq1
    anbi12d
    rspcev
    syl2anc
    3expib
    ralrimivv
    3ad2ant2
    @0
    @1
    @3
    @2
    @10
    wa
    wb
    @2
    vx
    vy
    vz
    cA
    cB
    cC
    cX
    cY
    fness.1
    fness.2
    isfne2
    3ad2ant1
    mpbir2and
end
