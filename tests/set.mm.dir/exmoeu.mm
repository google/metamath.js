include "wex.mm"
include "wmo.mm"
include "weu.mm"
include "wi.mm"
include "df-mo.mm"
include "biimpi.mm"
include "com12.mm"
include "exmo.mm"
include "ori.mm"
include "con1i.mm"
include "euex.mm"
include "ja.mm"
include "impbii.mm"

theorem exmoeu
  let wph: wff ph
  let vx: setvar x


  assert |- ( E. x ph <-> ( E* x ph -> E! x ph ) )

  proof
    wph
    vx
    wex
    #
    wph
    vx
    wmo
    #
    wph
    vx
    weu
    #
    wi
    @1
    @0
    @2
    @1
    @0
    @2
    wi
    wph
    vx
    df-mo
    biimpi
    com12
    @1
    @2
    @0
    @0
    @1
    @0
    @1
    wph
    vx
    exmo
    ori
    con1i
    wph
    vx
    euex
    ja
    impbii
end
