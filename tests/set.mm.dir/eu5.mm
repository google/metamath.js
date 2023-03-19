include "wex.mm"
include "weu.mm"
include "wa.mm"
include "wi.mm"
include "wmo.mm"
include "abai.mm"
include "euex.mm"
include "pm4.71ri.mm"
include "df-mo.mm"
include "anbi2i.mm"
include "3bitr4i.mm"

theorem eu5
  let wph: wff ph
  let vx: setvar x


  assert |- ( E! x ph <-> ( E. x ph /\ E* x ph ) )

  proof
    wph
    vx
    wex
    #
    wph
    vx
    weu
    #
    wa
    @0
    @0
    @1
    wi
    #
    wa
    @1
    @0
    wph
    vx
    wmo
    #
    wa
    @0
    @1
    abai
    @1
    @0
    wph
    vx
    euex
    pm4.71ri
    @3
    @2
    @0
    wph
    vx
    df-mo
    anbi2i
    3bitr4i
end
