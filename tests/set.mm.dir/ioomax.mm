include "cmnf.mm"
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
include "mnfxr.mm"
include "pnfxr.mm"
include "iooval2.mm"
include "mp2an.mm"
include "rabid2.mm"
include "mnflt.mm"
include "ltpnf.mm"
include "jca.mm"
include "mprgbir.mm"
include "eqtr4i.mm"

theorem ioomax
  let vx: setvar x


  assert |- ( -oo (,) +oo ) = RR

  proof
    cmnf
    cpnf
    cioo
    co
    #
    cmnf
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
    cr
    cmnf
    cxr
    wcel
    cpnf
    cxr
    wcel
    @0
    @5
    wceq
    mnfxr
    pnfxr
    vx
    cmnf
    cpnf
    iooval2
    mp2an
    cr
    @5
    wceq
    @4
    vx
    cr
    @4
    vx
    cr
    rabid2
    @1
    cr
    wcel
    @2
    @3
    @1
    mnflt
    @1
    ltpnf
    jca
    mprgbir
    eqtr4i
end
