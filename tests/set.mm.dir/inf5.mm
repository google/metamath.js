include "com.mm"
include "cvv.mm"
include "wcel.mm"
include "cv.mm"
include "cuni.mm"
include "wpss.mm"
include "wex.mm"
include "omex.mm"
include "infeq5i.mm"
include "ax-mp.mm"

theorem inf5
  let vx: setvar x


  assert |- E. x x C. U. x

  proof
    com
    cvv
    wcel
    vx
    cv
    #
    @0
    cuni
    wpss
    vx
    wex
    omex
    vx
    infeq5i
    ax-mp
end
