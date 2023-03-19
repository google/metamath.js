include "wi.mm"
include "frege9.mm"
include "frege18.mm"
include "ax-mp.mm"

theorem frege19
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( ch -> th ) -> ( ph -> ( ps -> th ) ) ) )

  proof
    wps
    wch
    wi
    #
    wch
    wth
    wi
    #
    wps
    wth
    wi
    #
    wi
    wi
    wph
    @0
    wi
    @1
    wph
    @2
    wi
    wi
    wi
    wps
    wch
    wth
    frege9
    @0
    @1
    @2
    wph
    frege18
    ax-mp
end
