include "wex.mm"
include "weu.mm"
include "wi.mm"
include "wmo.mm"
include "pm5.4.mm"
include "df-mo.mm"
include "imbi2i.mm"
include "3bitr4ri.mm"

theorem moabs
  let wph: wff ph
  let vx: setvar x


  assert |- ( E* x ph <-> ( E. x ph -> E* x ph ) )

  proof
    wph
    vx
    wex
    #
    @0
    wph
    vx
    weu
    #
    wi
    #
    wi
    @2
    @0
    wph
    vx
    wmo
    #
    wi
    @3
    @0
    @1
    pm5.4
    @3
    @2
    @0
    wph
    vx
    df-mo
    #
    imbi2i
    @4
    3bitr4ri
end
