include "wex.mm"
include "wn.mm"
include "weu.mm"
include "wi.mm"
include "wmo.mm"
include "pm2.21.mm"
include "df-mo.mm"
include "sylibr.mm"

theorem nexmo
  let wph: wff ph
  let vx: setvar x


  assert |- ( -. E. x ph -> E* x ph )

  proof
    wph
    vx
    wex
    #
    wn
    @0
    wph
    vx
    weu
    #
    wi
    wph
    vx
    wmo
    @0
    @1
    pm2.21
    wph
    vx
    df-mo
    sylibr
end
