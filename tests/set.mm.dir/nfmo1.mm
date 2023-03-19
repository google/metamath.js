include "wmo.mm"
include "wex.mm"
include "weu.mm"
include "wi.mm"
include "df-mo.mm"
include "nfe1.mm"
include "nfeu1.mm"
include "nfim.mm"
include "nfxfr.mm"

theorem nfmo1
  let wph: wff ph
  let vx: setvar x


  assert |- F/ x E* x ph

  proof
    wph
    vx
    wmo
    wph
    vx
    wex
    #
    wph
    vx
    weu
    #
    wi
    vx
    wph
    vx
    df-mo
    @0
    @1
    vx
    wph
    vx
    nfe1
    wph
    vx
    nfeu1
    nfim
    nfxfr
end
