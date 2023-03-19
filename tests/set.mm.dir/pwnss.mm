include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "wnel.mm"
include "crab.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "wb.mm"
include "wceq.mm"
include "eleq12.mm"
include "anidms.mm"
include "notbid.mm"
include "df-nel.mm"
include "syl5bb.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "pclem6.mm"
include "ax-mp.mm"
include "ssel.mm"
include "mtoi.mm"
include "ssrab2.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "nsyl3.mm"

theorem pwnss
  let cA: class A
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( A e. V -> -. ~P A C_ A )

  proof
    cA
    cpw
    #
    cA
    wss
    #
    vx
    cv
    #
    @2
    wnel
    #
    vx
    cA
    crab
    #
    @0
    wcel
    #
    cA
    cV
    wcel
    #
    @1
    @5
    @4
    cA
    wcel
    #
    @4
    @4
    wcel
    #
    @7
    @8
    wn
    #
    wa
    wb
    @7
    wn
    vy
    cv
    #
    @10
    wcel
    #
    wn
    #
    @9
    vy
    @4
    cA
    @4
    @10
    @4
    wceq
    #
    @11
    @8
    @13
    @11
    @8
    wb
    @10
    @4
    @10
    @4
    eleq12
    anidms
    notbid
    @3
    @12
    vx
    vy
    cA
    @3
    @2
    @2
    wcel
    #
    wn
    @2
    @10
    wceq
    #
    @12
    @2
    @2
    df-nel
    @15
    @14
    @11
    @15
    @14
    @11
    wb
    @2
    @10
    @2
    @10
    eleq12
    anidms
    notbid
    syl5bb
    cbvrabv
    elrab2
    @8
    @7
    pclem6
    ax-mp
    @0
    cA
    @4
    ssel
    mtoi
    @6
    @5
    @4
    cA
    wss
    @3
    vx
    cA
    ssrab2
    @4
    cA
    cV
    elpw2g
    mpbiri
    nsyl3
end
