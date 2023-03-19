include "cpw.mm"
include "crpss.mm"
include "ccnv.mm"
include "whe.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "dfhe3.mm"
include "wss.mm"
include "wpss.mm"
include "sstr2.mm"
include "pssss.mm"
include "syl11.mm"
include "alrimiv.mm"
include "selpw.mm"
include "vex.mm"
include "brcnv.mm"
include "brrpss.mm"
include "bitri.mm"
include "imbi12i.mm"
include "albii.mm"
include "3imtr4i.mm"
include "mpgbir.mm"

theorem psshepw
  let cA: class A
  let vx: setvar x
  let vy: setvar y


  assert |- `' [C.] hereditary ~P A

  proof
    cA
    cpw
    #
    crpss
    ccnv
    #
    whe
    vx
    cv
    #
    @0
    wcel
    #
    @2
    vy
    cv
    #
    @1
    wbr
    #
    @4
    @0
    wcel
    #
    wi
    #
    vy
    wal
    #
    wi
    vx
    vx
    vy
    @0
    @1
    dfhe3
    @2
    cA
    wss
    #
    @4
    @2
    wpss
    #
    @4
    cA
    wss
    #
    wi
    #
    vy
    wal
    @3
    @8
    @9
    @12
    vy
    @4
    @2
    wss
    @9
    @11
    @10
    @4
    @2
    cA
    sstr2
    @4
    @2
    pssss
    syl11
    alrimiv
    vx
    cA
    selpw
    @7
    @12
    vy
    @5
    @10
    @6
    @11
    @5
    @4
    @2
    crpss
    wbr
    @10
    @2
    @4
    crpss
    vx
    vex
    #
    vy
    vex
    brcnv
    @4
    @2
    @13
    brrpss
    bitri
    vy
    cA
    selpw
    imbi12i
    albii
    3imtr4i
    mpgbir
end
