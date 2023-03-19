include "cc0.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cr.mm"
include "crab.mm"
include "cxr.mm"
include "wcel.mm"
include "wceq.mm"
include "0xr.mm"
include "pnfxr.mm"
include "iooval2.mm"
include "mp2an.mm"
include "ltpnf.mm"
include "biantrud.mm"
include "rabbiia.mm"
include "eqtr4i.mm"

theorem ioopos
  let vx: setvar x


  assert |- ( 0 (,) +oo ) = { x e. RR | 0 < x }

  proof
    cc0
    cpnf
    cioo
    co
    #
    cc0
    vx
    cv
    #
    clt
    wbr
    #
    @1
    cpnf
    clt
    wbr
    #
    wa
    #
    vx
    cr
    crab
    #
    @2
    vx
    cr
    crab
    cc0
    cxr
    wcel
    cpnf
    cxr
    wcel
    @0
    @5
    wceq
    0xr
    pnfxr
    vx
    cc0
    cpnf
    iooval2
    mp2an
    @2
    @4
    vx
    cr
    @1
    cr
    wcel
    @3
    @2
    @1
    ltpnf
    biantrud
    rabbiia
    eqtr4i
end
