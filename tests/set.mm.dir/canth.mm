include "cpw.mm"
include "wfo.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wn.mm"
include "crab.mm"
include "crn.mm"
include "wss.mm"
include "ssrab2.mm"
include "elpw2.mm"
include "mpbir.mm"
include "forn.mm"
include "syl5eleqr.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "id.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "notbid.mm"
include "elrab.mm"
include "baibr.mm"
include "nbbn.mm"
include "sylib.mm"
include "eleq2.mm"
include "nsyl.mm"
include "nrex.mm"
include "wfn.mm"
include "fofn.mm"
include "fvelrnb.mm"
include "syl.mm"
include "mtbiri.mm"
include "pm2.65i.mm"

theorem canth
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  assume canth.1: |- A e. _V


  assert |- -. F : A -onto-> ~P A

  proof
    cA
    cA
    cpw
    #
    cF
    wfo
    #
    vx
    cv
    #
    @2
    cF
    cfv
    #
    wcel
    #
    wn
    #
    vx
    cA
    crab
    #
    cF
    crn
    #
    wcel
    #
    @1
    @6
    @0
    @7
    @6
    @0
    wcel
    @6
    cA
    wss
    @5
    vx
    cA
    ssrab2
    @6
    cA
    canth.1
    elpw2
    mpbir
    cA
    @0
    cF
    forn
    syl5eleqr
    @1
    @8
    vy
    cv
    #
    cF
    cfv
    #
    @6
    wceq
    #
    vy
    cA
    wrex
    #
    @11
    vy
    cA
    @9
    cA
    wcel
    #
    @9
    @10
    wcel
    #
    @9
    @6
    wcel
    #
    wb
    #
    @11
    @13
    @14
    wn
    #
    @15
    wb
    @16
    wn
    @15
    @13
    @17
    @5
    @17
    vx
    @9
    cA
    @2
    @9
    wceq
    #
    @4
    @14
    @18
    @2
    @9
    @3
    @10
    @18
    id
    @2
    @9
    cF
    fveq2
    eleq12d
    notbid
    elrab
    baibr
    @14
    @15
    nbbn
    sylib
    @10
    @6
    @9
    eleq2
    nsyl
    nrex
    @1
    cF
    cA
    wfn
    @8
    @12
    wb
    cA
    @0
    cF
    fofn
    vy
    cA
    @6
    cF
    fvelrnb
    syl
    mtbiri
    pm2.65i
end
