include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "char.mm"
include "cfv.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "wn.mm"
include "harndom.mm"
include "wb.mm"
include "con0.mm"
include "harcl.mm"
include "onenon.mm"
include "ax-mp.mm"
include "wa.mm"
include "domtri2.mm"
include "con2bid.mm"
include "mpan.mm"
include "mpbiri.mm"

theorem harsdom
  let cA: class A


  assert |- ( A e. dom card -> A ~< ( har ` A ) )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cA
    cA
    char
    cfv
    #
    csdm
    wbr
    #
    @2
    cA
    cdom
    wbr
    #
    wn
    #
    cA
    harndom
    @2
    @0
    wcel
    #
    @1
    @3
    @5
    wb
    @2
    con0
    wcel
    @6
    cA
    harcl
    @2
    onenon
    ax-mp
    @6
    @1
    wa
    @4
    @3
    @2
    cA
    domtri2
    con2bid
    mpan
    mpbiri
end
