include "cc0.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "crab.mm"
include "crp.mm"
include "ioopos.mm"
include "df-rp.mm"
include "eqtr4i.mm"

theorem ioorp
  let vx: setvar x


  assert |- ( 0 (,) +oo ) = RR+

  proof
    cc0
    cpnf
    cioo
    co
    cc0
    vx
    cv
    clt
    wbr
    vx
    cr
    crab
    crp
    vx
    ioopos
    vx
    df-rp
    eqtr4i
end
