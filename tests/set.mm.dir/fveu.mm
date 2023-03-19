include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "cfv.mm"
include "cio.mm"
include "cab.mm"
include "cuni.mm"
include "df-fv.mm"
include "iotauni.mm"
include "syl5eq.mm"

theorem fveu
  let vx: setvar x
  let cA: class A
  let cF: class F

  disjoint F x
  disjoint A x
  assert |- ( E! x A F x -> ( F ` A ) = U. { x | A F x } )

  proof
    cA
    vx
    cv
    cF
    wbr
    #
    vx
    weu
    cA
    cF
    cfv
    @0
    vx
    cio
    @0
    vx
    cab
    cuni
    vx
    cA
    cF
    df-fv
    @0
    vx
    iotauni
    syl5eq
end
