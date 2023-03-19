include "wnf.mm"
include "wal.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "wsb.mm"
include "wmo.mm"
include "wl-sb8et.mm"
include "wl-sb8eut.mm"
include "imbi12d.mm"
include "df-mo.mm"
include "3bitr4g.mm"

theorem wl-sb8mot
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y


  assert |- ( A. x F/ y ph -> ( E* x ph <-> E* y [ y / x ] ph ) )

  proof
    wph
    vy
    wnf
    vx
    wal
    #
    wph
    vx
    wex
    #
    wph
    vx
    weu
    #
    wi
    wph
    vx
    vy
    wsb
    #
    vy
    wex
    #
    @3
    vy
    weu
    #
    wi
    wph
    vx
    wmo
    @3
    vy
    wmo
    @0
    @1
    @4
    @2
    @5
    wph
    vx
    vy
    wl-sb8et
    wph
    vx
    vy
    wl-sb8eut
    imbi12d
    wph
    vx
    df-mo
    @3
    vy
    df-mo
    3bitr4g
end
