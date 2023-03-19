include "cvol.mm"
include "cdm.mm"
include "cuni.mm"
include "cr.mm"
include "wss.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "unissb.mm"
include "mblss.mm"
include "mprgbir.mm"
include "rembl.mm"
include "unissel.mm"
include "mp2an.mm"

theorem unidmvol
  let vx: setvar x


  assert |- U. dom vol = RR

  proof
    cvol
    cdm
    #
    cuni
    #
    cr
    wss
    #
    cr
    @0
    wcel
    @1
    cr
    wceq
    @2
    vx
    cv
    #
    cr
    wss
    vx
    @0
    vx
    @0
    cr
    unissb
    @3
    mblss
    mprgbir
    rembl
    @0
    cr
    unissel
    mp2an
end
