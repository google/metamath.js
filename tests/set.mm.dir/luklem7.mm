include "wi.mm"
include "luk-1.mm"
include "luklem5.mm"
include "luklem1.mm"
include "luklem6.mm"
include "ax-mp.mm"

theorem luklem7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ps -> ( ph -> ch ) ) )

  proof
    wph
    wps
    wch
    wi
    #
    wi
    @0
    wch
    wi
    #
    wph
    wch
    wi
    #
    wi
    #
    wps
    @2
    wi
    #
    wph
    @0
    wch
    luk-1
    wps
    @1
    wi
    @3
    @4
    wi
    wps
    @0
    @1
    wi
    #
    @1
    wps
    @0
    wps
    wi
    @5
    wps
    @0
    luklem5
    @0
    wps
    wch
    luk-1
    luklem1
    @0
    wch
    luklem6
    luklem1
    wps
    @1
    @2
    luk-1
    ax-mp
    luklem1
end
