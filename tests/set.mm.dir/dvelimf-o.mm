include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wi.mm"
include "hba1-o.mm"
include "ax-c11.mm"
include "aecoms-o.mm"
include "syl5.mm"
include "a1d.mm"
include "wa.mm"
include "hbnae-o.mm"
include "hban.mm"
include "ax-c9.mm"
include "imp.mm"
include "a1i.mm"
include "hbimd.mm"
include "hbald.mm"
include "ex.mm"
include "pm2.61i.mm"
include "equsalh.mm"
include "albii.mm"
include "3imtr3g.mm"

theorem dvelimf-o
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume dvelimf-o.1: |- ( ph -> A. x ph )
  assume dvelimf-o.2: |- ( ps -> A. z ps )
  assume dvelimf-o.3: |- ( z = y -> ( ph <-> ps ) )


  assert |- ( -. A. x x = y -> ( ps -> A. x ps ) )

  proof
    vx
    vy
    weq
    vx
    wal
    wn
    #
    vz
    vy
    weq
    #
    wph
    wi
    #
    vz
    wal
    #
    @3
    vx
    wal
    #
    wps
    wps
    vx
    wal
    vx
    vz
    weq
    vx
    wal
    #
    @0
    @3
    @4
    wi
    #
    wi
    @5
    @6
    @0
    @3
    @3
    vz
    wal
    #
    @5
    @4
    @2
    vz
    hba1-o
    @7
    @4
    wi
    vz
    vx
    @3
    vz
    vx
    ax-c11
    aecoms-o
    syl5
    a1d
    @5
    wn
    #
    @0
    @6
    @8
    @0
    wa
    #
    @2
    vx
    vz
    @8
    @0
    vz
    vx
    vz
    vz
    hbnae-o
    vx
    vy
    vz
    hbnae-o
    hban
    @9
    @1
    wph
    vx
    @8
    @0
    vx
    vx
    vz
    vx
    hbnae-o
    vx
    vy
    vx
    hbnae-o
    hban
    @8
    @0
    @1
    @1
    vx
    wal
    wi
    vz
    vy
    vx
    ax-c9
    imp
    wph
    wph
    vx
    wal
    wi
    @9
    dvelimf-o.1
    a1i
    hbimd
    hbald
    ex
    pm2.61i
    wph
    wps
    vz
    vy
    dvelimf-o.2
    dvelimf-o.3
    equsalh
    #
    @3
    wps
    vx
    @10
    albii
    3imtr3g
end
