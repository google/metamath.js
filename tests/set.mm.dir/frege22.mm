include "wi.mm"
include "frege16.mm"
include "frege5.mm"
include "ax-mp.mm"

theorem frege22
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et


  assert |- ( ( ph -> ( ps -> ( ch -> ( th -> ( ta -> et ) ) ) ) ) -> ( ph -> ( ps -> ( ch -> ( ta -> ( th -> et ) ) ) ) ) )

  proof
    wps
    wch
    wth
    wta
    wet
    wi
    wi
    wi
    wi
    #
    wps
    wch
    wta
    wth
    wet
    wi
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
    wet
    frege16
    @0
    @1
    wph
    frege5
    ax-mp
end
