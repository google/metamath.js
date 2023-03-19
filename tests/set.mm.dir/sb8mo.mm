include "wex.mm"
include "weu.mm"
include "wi.mm"
include "wsb.mm"
include "wmo.mm"
include "sb8e.mm"
include "sb8eu.mm"
include "imbi12i.mm"
include "df-mo.mm"
include "3bitr4i.mm"

theorem sb8mo
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vz: setvar z
  assume sb8eu.1: |- F/ y ph


  assert |- ( E* x ph <-> E* y [ y / x ] ph )

  proof
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
    @2
    vy
    weu
    #
    wi
    wph
    vx
    wmo
    @2
    vy
    wmo
    @0
    @3
    @1
    @4
    wph
    vx
    vy
    sb8eu.1
    sb8e
    wph
    vx
    vy
    sb8eu.1
    sb8eu
    imbi12i
    wph
    vx
    df-mo
    @2
    vy
    df-mo
    3bitr4i
end
