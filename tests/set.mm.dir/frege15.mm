include "wi.mm"
include "frege14.mm"
include "frege12.mm"
include "ax-mp.mm"

theorem frege15
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph -> ( ps -> ( ch -> ( th -> ta ) ) ) ) -> ( th -> ( ph -> ( ps -> ( ch -> ta ) ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wta
    wi
    wi
    wi
    wi
    #
    wph
    wth
    wps
    wch
    wta
    wi
    wi
    #
    wi
    wi
    wi
    @0
    wth
    wph
    @1
    wi
    wi
    wi
    wph
    wps
    wch
    wth
    wta
    frege14
    @0
    wph
    wth
    @1
    frege12
    ax-mp
end
