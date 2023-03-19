include "wcel.mm"
include "cv.mm"
include "wa.mm"
include "wal.mm"
include "wceq.mm"
include "wex.mm"
include "cab.mm"
include "cvv.mm"
include "vprc.mm"
include "wral.mm"
include "wrex.mm"
include "alral.mm"
include "rexv.mm"
include "bicomi.mm"
include "abbii.mm"
include "eleq1i.mm"
include "biimpi.mm"
include "abnexg.mm"
include "syl2im.mm"
include "mtoi.mm"

theorem abnex
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cV: class V

  disjoint x y
  disjoint F y
  assert |- ( A. x ( F e. V /\ x e. F ) -> -. { y | E. x y = F } e. _V )

  proof
    cF
    cV
    wcel
    vx
    cv
    cF
    wcel
    wa
    #
    vx
    wal
    #
    vy
    cv
    cF
    wceq
    #
    vx
    wex
    #
    vy
    cab
    #
    cvv
    wcel
    #
    cvv
    cvv
    wcel
    #
    vprc
    @1
    @0
    vx
    cvv
    wral
    @5
    @2
    vx
    cvv
    wrex
    #
    vy
    cab
    #
    cvv
    wcel
    #
    @6
    @0
    vx
    cvv
    alral
    @5
    @9
    @4
    @8
    cvv
    @3
    @7
    vy
    @7
    @3
    @2
    vx
    rexv
    bicomi
    abbii
    eleq1i
    biimpi
    vx
    vy
    cvv
    cF
    cV
    cvv
    abnexg
    syl2im
    mtoi
end
