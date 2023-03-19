include "cv.mm"
include "wceq.mm"
include "wb.mm"
include "cio.mm"
include "iotaval.mm"
include "biid.mm"
include "mpg.mm"

theorem iotaequ
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( iota x x = y ) = y

  proof
    vx
    cv
    vy
    cv
    #
    wceq
    #
    @1
    wb
    @1
    vx
    cio
    @0
    wceq
    vx
    @1
    vx
    vy
    iotaval
    @1
    biid
    mpg
end
