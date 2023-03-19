include "wi.mm"
include "frege19.mm"
include "frege18.mm"
include "ax-mp.mm"

theorem frege20
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph -> ( ps -> ( ch -> th ) ) ) -> ( ( th -> ta ) -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) )

  proof
    wps
    wch
    wth
    wi
    wi
    #
    wth
    wta
    wi
    #
    wps
    wch
    wta
    wi
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
    wta
    frege19
    @0
    @1
    @2
    wph
    frege18
    ax-mp
end
