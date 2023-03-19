include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wsb.mm"
include "wl-ax11-lem8.mm"
include "wl-ax11-lem6.mm"
include "bitr3d.mm"
include "biimpd.mm"
include "ex.mm"
include "aecoms.mm"

theorem wl-ax11-lem10
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u

  disjoint u x
  assert |- ( A. y y = u -> ( -. A. x x = y -> ( A. y A. x ph -> A. x A. y ph ) ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    #
    wph
    vx
    wal
    vy
    wal
    #
    wph
    vy
    wal
    vx
    wal
    #
    wi
    #
    wi
    vu
    vy
    vu
    vy
    weq
    vu
    wal
    #
    @0
    @3
    @4
    @0
    wa
    #
    @1
    @2
    @5
    wph
    vy
    vu
    wsb
    vx
    wal
    vu
    wal
    @1
    @2
    wph
    vx
    vy
    vu
    wl-ax11-lem8
    wph
    vx
    vy
    vu
    wl-ax11-lem6
    bitr3d
    biimpd
    ex
    aecoms
end
