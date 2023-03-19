include "cvv.mm"
include "wcel.mm"
include "wn.mm"
include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "brprcneu.mm"
include "tz6.12-2.mm"
include "syl.mm"

theorem fvprc
  let cA: class A
  let cF: class F
  let vx: setvar x


  assert |- ( -. A e. _V -> ( F ` A ) = (/) )

  proof
    cA
    cvv
    wcel
    wn
    cA
    vx
    cv
    cF
    wbr
    vx
    weu
    wn
    cA
    cF
    cfv
    c0
    wceq
    vx
    cA
    cF
    brprcneu
    vx
    cA
    cF
    tz6.12-2
    syl
end
