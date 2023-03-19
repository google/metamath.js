include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "wn.mm"
include "cfv.mm"
include "cio.mm"
include "c0.mm"
include "df-fv.mm"
include "iotanul.mm"
include "syl5eq.mm"

theorem tz6.12-2
  let vx: setvar x
  let cA: class A
  let cF: class F

  disjoint F x
  disjoint A x
  assert |- ( -. E! x A F x -> ( F ` A ) = (/) )

  proof
    cA
    vx
    cv
    cF
    wbr
    #
    vx
    weu
    wn
    cA
    cF
    cfv
    @0
    vx
    cio
    c0
    vx
    cA
    cF
    df-fv
    @0
    vx
    iotanul
    syl5eq
end
