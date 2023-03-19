include "cwina.mm"
include "wcel.mm"
include "com.mm"
include "wss.mm"
include "wlim.mm"
include "winainf.mm"
include "ccrd.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "winacard.mm"
include "cardlim.mm"
include "sseq2.mm"
include "limeq.mm"
include "bibi12d.mm"
include "mpbii.mm"
include "syl.mm"
include "mpbid.mm"

theorem winalim
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( A e. InaccW -> Lim A )

  proof
    cA
    cwina
    wcel
    #
    com
    cA
    wss
    #
    cA
    wlim
    #
    cA
    winainf
    @0
    cA
    ccrd
    cfv
    #
    cA
    wceq
    #
    @1
    @2
    wb
    #
    cA
    winacard
    @4
    com
    @3
    wss
    #
    @3
    wlim
    #
    wb
    @5
    cA
    cardlim
    @4
    @6
    @1
    @7
    @2
    @3
    cA
    com
    sseq2
    @3
    cA
    limeq
    bibi12d
    mpbii
    syl
    mpbid
end
