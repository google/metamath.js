include "wn.mm"
include "wi.mm"
include "luk-1.mm"
include "luk-3.mm"
include "ax-mp.mm"
include "luklem1.mm"

theorem luklem2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> -. ps ) -> ( ( ( ph -> ch ) -> th ) -> ( ps -> th ) ) )

  proof
    wph
    wps
    wn
    #
    wi
    #
    wps
    wph
    wch
    wi
    #
    wi
    #
    @2
    wth
    wi
    wps
    wth
    wi
    wi
    @1
    @0
    wch
    wi
    #
    @2
    wi
    #
    @3
    wph
    @0
    wch
    luk-1
    wps
    @4
    wi
    @5
    @3
    wi
    wps
    wch
    luk-3
    wps
    @4
    @2
    luk-1
    ax-mp
    luklem1
    wps
    @2
    wth
    luk-1
    luklem1
end
