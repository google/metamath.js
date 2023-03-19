include "wcel.mm"
include "cpw.mm"
include "ccld.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "cdif.mm"
include "wa.mm"
include "ctop.mm"
include "wb.mm"
include "distop.mm"
include "cuni.mm"
include "unipw.mm"
include "eqcomi.mm"
include "iscld.mm"
include "syl.mm"
include "difss.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "biantrud.mm"
include "bitr4d.mm"
include "selpw.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem discld
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( Clsd ` ~P A ) = ~P A )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cpw
    #
    ccld
    cfv
    #
    @1
    @0
    vx
    cv
    #
    @2
    wcel
    #
    @3
    cA
    wss
    #
    @3
    @1
    wcel
    @0
    @4
    @5
    cA
    @3
    cdif
    #
    @1
    wcel
    #
    wa
    #
    @5
    @0
    @1
    ctop
    wcel
    @4
    @8
    wb
    cA
    cV
    distop
    @3
    @1
    cA
    @1
    cuni
    cA
    cA
    unipw
    eqcomi
    iscld
    syl
    @0
    @7
    @5
    @0
    @7
    @6
    cA
    wss
    cA
    @3
    difss
    @6
    cA
    cV
    elpw2g
    mpbiri
    biantrud
    bitr4d
    vx
    cA
    selpw
    syl6bbr
    eqrdv
end
