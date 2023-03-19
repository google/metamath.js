include "wi.mm"
include "frege18.mm"
include "frege22.mm"
include "ax-mp.mm"

theorem frege23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ph -> ( ps -> ( ch -> th ) ) ) -> ( ( ta -> ph ) -> ( ps -> ( ch -> ( ta -> th ) ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    #
    wi
    wi
    #
    wta
    wph
    wi
    #
    wps
    wta
    @0
    wi
    wi
    wi
    wi
    @1
    @2
    wps
    wch
    wta
    wth
    wi
    wi
    wi
    wi
    wi
    wph
    wps
    @0
    wta
    frege18
    @1
    @2
    wps
    wta
    wch
    wth
    frege22
    ax-mp
end
