include "cmnf.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxr.mm"
include "crab.mm"
include "wcel.mm"
include "wceq.mm"
include "mnfxr.mm"
include "pnfxr.mm"
include "iccval.mm"
include "mp2an.mm"
include "rabid2.mm"
include "mnfle.mm"
include "pnfge.mm"
include "jca.mm"
include "mprgbir.mm"
include "eqtr4i.mm"

theorem iccmax
  let vx: setvar x


  assert |- ( -oo [,] +oo ) = RR*

  proof
    cmnf
    cpnf
    cicc
    co
    #
    cmnf
    vx
    cv
    #
    cle
    wbr
    #
    @1
    cpnf
    cle
    wbr
    #
    wa
    #
    vx
    cxr
    crab
    #
    cxr
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
    iccval
    mp2an
    cxr
    @5
    wceq
    @4
    vx
    cxr
    @4
    vx
    cxr
    rabid2
    @1
    cxr
    wcel
    @2
    @3
    @1
    mnfle
    @1
    pnfge
    jca
    mprgbir
    eqtr4i
end
