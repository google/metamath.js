include "cr.mm"
include "cv.mm"
include "wwe.mm"
include "wex.mm"
include "cvol.mm"
include "cdm.mm"
include "cpw.mm"
include "wpss.mm"
include "cvv.mm"
include "wcel.mm"
include "reex.mm"
include "weth.mm"
include "ax-mp.mm"
include "vitali.mm"
include "exlimiv.mm"

theorem vitali2
  let vk: setvar k
  let vx: setvar x
  let vo: setvar o


  assert |- dom vol C. ~P RR

  proof
    cr
    vo
    cv
    #
    wwe
    #
    vo
    wex
    #
    cvol
    cdm
    cr
    cpw
    wpss
    #
    cr
    cvv
    wcel
    @2
    reex
    vo
    cr
    cvv
    weth
    ax-mp
    @1
    @3
    vo
    @0
    vitali
    exlimiv
    ax-mp
end
