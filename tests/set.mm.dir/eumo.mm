include "weu.mm"
include "wex.mm"
include "wi.mm"
include "wmo.mm"
include "ax-1.mm"
include "df-mo.mm"
include "sylibr.mm"

theorem eumo
  let wph: wff ph
  let vx: setvar x


  assert |- ( E! x ph -> E* x ph )

  proof
    wph
    vx
    weu
    #
    wph
    vx
    wex
    #
    @0
    wi
    wph
    vx
    wmo
    @0
    @1
    ax-1
    wph
    vx
    df-mo
    sylibr
end
