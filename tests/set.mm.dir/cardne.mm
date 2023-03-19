include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "cfv.mm"
include "cen.mm"
include "wbr.mm"
include "wn.mm"
include "elfvdm.mm"
include "wi.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "cardon.mm"
include "oneli.mm"
include "breq1.mm"
include "onintss.mm"
include "syl.mm"
include "adantl.mm"
include "wb.mm"
include "cardval3.mm"
include "sseq1d.mm"
include "adantr.mm"
include "sylibrd.mm"
include "ontri1.mm"
include "sylancr.mm"
include "sylibd.mm"
include "con2d.mm"
include "ex.mm"
include "pm2.43d.mm"
include "mpcom.mm"

theorem cardne
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( A e. ( card ` B ) -> -. A ~~ B )

  proof
    cB
    ccrd
    cdm
    wcel
    #
    cA
    cB
    ccrd
    cfv
    #
    wcel
    #
    cA
    cB
    cen
    wbr
    #
    wn
    #
    cA
    cB
    ccrd
    elfvdm
    @0
    @2
    @4
    @0
    @2
    @2
    @4
    wi
    @0
    @2
    wa
    #
    @3
    @2
    @5
    @3
    @1
    cA
    wss
    #
    @2
    wn
    #
    @5
    @3
    vx
    cv
    #
    cB
    cen
    wbr
    #
    vx
    con0
    crab
    cint
    #
    cA
    wss
    #
    @6
    @2
    @3
    @11
    wi
    #
    @0
    @2
    cA
    con0
    wcel
    #
    @12
    @1
    cA
    cB
    cardon
    #
    oneli
    #
    @9
    @3
    vx
    cA
    @8
    cA
    cB
    cen
    breq1
    onintss
    syl
    adantl
    @0
    @6
    @11
    wb
    @2
    @0
    @1
    @10
    cA
    vx
    cB
    cardval3
    sseq1d
    adantr
    sylibrd
    @2
    @6
    @7
    wb
    #
    @0
    @2
    @1
    con0
    wcel
    @13
    @16
    @14
    @15
    @1
    cA
    ontri1
    sylancr
    adantl
    sylibd
    con2d
    ex
    pm2.43d
    mpcom
end
