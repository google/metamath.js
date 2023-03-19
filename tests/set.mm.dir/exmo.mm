include "wex.mm"
include "wmo.mm"
include "wn.mm"
include "weu.mm"
include "wi.mm"
include "pm2.21.mm"
include "df-mo.mm"
include "sylibr.mm"
include "orri.mm"

theorem exmo
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x ph \/ E* x ph )

  proof
    wph
    vx
    wex
    #
    wph
    vx
    wmo
    #
    @0
    wn
    @0
    wph
    vx
    weu
    #
    wi
    @1
    @0
    @2
    pm2.21
    wph
    vx
    df-mo
    sylibr
    orri
end
