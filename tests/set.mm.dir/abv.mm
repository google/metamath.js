include "cv.mm"
include "cab.mm"
include "wcel.mm"
include "wal.mm"
include "wsb.mm"
include "cvv.mm"
include "wceq.mm"
include "df-clab.mm"
include "albii.mm"
include "eqv.mm"
include "nfv.mm"
include "sb8.mm"
include "3bitr4i.mm"

theorem abv
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( { x | ph } = _V <-> A. x ph )

  proof
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
    wph
    vx
    vy
    wsb
    #
    vy
    wal
    @0
    cvv
    wceq
    wph
    vx
    wal
    @1
    @2
    vy
    wph
    vy
    vx
    df-clab
    albii
    vy
    @0
    eqv
    wph
    vx
    vy
    wph
    vy
    nfv
    sb8
    3bitr4i
end
