include "wal.mm"
include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "cvv.mm"
include "wceq.mm"
include "ax-5.mm"
include "bj-vexwvt.mm"
include "alrimih.mm"
include "eqv.mm"
include "sylibr.mm"

theorem bj-abv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x ph -> { x | ph } = _V )

  proof
    wph
    vx
    wal
    #
    vy
    cv
    wph
    vx
    cab
    #
    wcel
    #
    vy
    wal
    @1
    cvv
    wceq
    @0
    @2
    vy
    @0
    vy
    ax-5
    wph
    vx
    vy
    bj-vexwvt
    alrimih
    vy
    @1
    eqv
    sylibr
end
