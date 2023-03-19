include "cvv.mm"
include "wcel.mm"
include "cdm.mm"
include "wn.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "wi.mm"
include "cv.mm"
include "wbr.mm"
include "weu.mm"
include "wex.mm"
include "euex.mm"
include "eldmg.mm"
include "syl5ibr.mm"
include "con3d.mm"
include "tz6.12-2.mm"
include "syl6.mm"
include "fvprc.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem ndmfv
  let cA: class A
  let cF: class F
  let vx: setvar x


  assert |- ( -. A e. dom F -> ( F ` A ) = (/) )

  proof
    cA
    cvv
    wcel
    #
    cA
    cF
    cdm
    wcel
    #
    wn
    #
    cA
    cF
    cfv
    c0
    wceq
    #
    wi
    @0
    @2
    cA
    vx
    cv
    cF
    wbr
    #
    vx
    weu
    #
    wn
    @3
    @0
    @5
    @1
    @5
    @1
    @0
    @4
    vx
    wex
    @4
    vx
    euex
    vx
    cA
    cF
    cvv
    eldmg
    syl5ibr
    con3d
    vx
    cA
    cF
    tz6.12-2
    syl6
    @0
    wn
    @3
    @2
    cA
    cF
    fvprc
    a1d
    pm2.61i
end
