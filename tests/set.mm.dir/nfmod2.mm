include "wmo.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "df-mo.mm"
include "nfexd2.mm"
include "nfeud2.mm"
include "nfimd.mm"
include "nfxfrd.mm"

theorem nfmod2
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume nfmod2.1: |- F/ y ph
  assume nfmod2.2: |- ( ( ph /\ -. A. x x = y ) -> F/ x ps )


  assert |- ( ph -> F/ x E* y ps )

  proof
    wps
    vy
    wmo
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
    wps
    vy
    df-mo
    wph
    @0
    @1
    vx
    wph
    wps
    vx
    vy
    nfmod2.1
    nfmod2.2
    nfexd2
    wph
    wps
    vx
    vy
    nfmod2.1
    nfmod2.2
    nfeud2
    nfimd
    nfxfrd
end
