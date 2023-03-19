include "wnf.mm"
include "wal.mm"
include "wi.mm"
include "wsb.mm"
include "wl-sb8t.mm"
include "imbi2d.mm"
include "wb.mm"
include "19.21t.mm"
include "sps.mm"
include "bitr4d.mm"

theorem wl-sbhbt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x F/ y ph -> ( ( ph -> A. x ph ) <-> A. y ( ph -> [ y / x ] ph ) ) )

  proof
    wph
    vy
    wnf
    #
    vx
    wal
    #
    wph
    wph
    vx
    wal
    #
    wi
    wph
    wph
    vx
    vy
    wsb
    #
    vy
    wal
    #
    wi
    #
    wph
    @3
    wi
    vy
    wal
    #
    @1
    @2
    @4
    wph
    wph
    vx
    vy
    wl-sb8t
    imbi2d
    @0
    @6
    @5
    wb
    vx
    wph
    @3
    vy
    19.21t
    sps
    bitr4d
end
