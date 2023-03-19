include "wi.mm"
include "frege13.mm"
include "frege5.mm"
include "ax-mp.mm"

theorem frege14
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) -> ( ph -> ( th -> ( ps -> ( ch -> ta ) ) ) ) )

  proof
    wps
    wch
    wth
    wta
    wi
    wi
    wi
    #
    wth
    wps
    wch
    wta
    wi
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
    wta
    frege13
    @0
    @1
    wph
    frege5
    ax-mp
end
