include "wi.mm"
include "frege5.mm"
include "ax-mp.mm"

theorem frege6
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ( th -> ps ) -> ( th -> ch ) ) ) )

  proof
    wps
    wch
    wi
    #
    wth
    wps
    wi
    wth
    wch
    wi
    wi
    #
    wi
    wph
    @0
    wi
    wph
    @1
    wi
    wi
    wps
    wch
    wth
    frege5
    @0
    @1
    wph
    frege5
    ax-mp
end
