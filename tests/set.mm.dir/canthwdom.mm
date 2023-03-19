include "cpw.mm"
include "cwdom.mm"
include "wbr.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "c0.mm"
include "wne.mm"
include "wb.mm"
include "wcel.mm"
include "0elpw.mm"
include "ne0i.mm"
include "mp1i.mm"
include "brwdomn0.mm"
include "syl.mm"
include "ibi.mm"
include "cvv.mm"
include "wn.mm"
include "relwdom.mm"
include "brrelex2i.mm"
include "wceq.mm"
include "foeq2.mm"
include "pweq.mm"
include "foeq3.mm"
include "bitrd.mm"
include "notbid.mm"
include "vex.mm"
include "canth.mm"
include "vtoclg.mm"
include "nexdv.mm"
include "pm2.65i.mm"

theorem canthwdom
  let cA: class A
  let vf: setvar f
  let vx: setvar x


  assert |- -. ~P A ~<_* A

  proof
    cA
    cpw
    #
    cA
    cwdom
    wbr
    #
    cA
    @0
    vf
    cv
    #
    wfo
    #
    vf
    wex
    #
    @1
    @4
    @1
    @0
    c0
    wne
    #
    @1
    @4
    wb
    c0
    @0
    wcel
    @5
    @1
    cA
    0elpw
    @0
    c0
    ne0i
    mp1i
    vf
    @0
    cA
    brwdomn0
    syl
    ibi
    @1
    @3
    vf
    @1
    cA
    cvv
    wcel
    @3
    wn
    #
    @0
    cA
    cwdom
    relwdom
    brrelex2i
    vx
    cv
    #
    @7
    cpw
    #
    @2
    wfo
    #
    wn
    @6
    vx
    cA
    cvv
    @7
    cA
    wceq
    #
    @9
    @3
    @10
    @9
    cA
    @8
    @2
    wfo
    #
    @3
    @7
    cA
    @8
    @2
    foeq2
    @10
    @8
    @0
    wceq
    @11
    @3
    wb
    @7
    cA
    pweq
    @8
    @0
    cA
    @2
    foeq3
    syl
    bitrd
    notbid
    @7
    @2
    vx
    vex
    canth
    vtoclg
    syl
    nexdv
    pm2.65i
end
