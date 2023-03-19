include "wex.mm"
include "weu.mm"
include "wi.mm"
include "wmo.mm"
include "cbvex.mm"
include "cbveu.mm"
include "imbi12i.mm"
include "df-mo.mm"
include "3bitr4i.mm"

theorem cbvmo
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume cbvmo.1: |- F/ y ph
  assume cbvmo.2: |- F/ x ps
  assume cbvmo.3: |- ( x = y -> ( ph <-> ps ) )


  assert |- ( E* x ph <-> E* y ps )

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
    wps
    vy
    wex
    #
    wps
    vy
    weu
    #
    wi
    wph
    vx
    wmo
    wps
    vy
    wmo
    @0
    @2
    @1
    @3
    wph
    wps
    vx
    vy
    cbvmo.1
    cbvmo.2
    cbvmo.3
    cbvex
    wph
    wps
    vx
    vy
    cbvmo.1
    cbvmo.2
    cbvmo.3
    cbveu
    imbi12i
    wph
    vx
    df-mo
    wps
    vy
    df-mo
    3bitr4i
end
