include "wi.mm"
include "frege12.mm"
include "ax-mp.mm"

theorem frege13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ( ch -> th ) ) ) -> ( ch -> ( ph -> ( ps -> th ) ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wi
    wi
    #
    wph
    wch
    wps
    wth
    wi
    #
    wi
    wi
    wi
    @0
    wch
    wph
    @1
    wi
    wi
    wi
    wph
    wps
    wch
    wth
    frege12
    @0
    wph
    wch
    @1
    frege12
    ax-mp
end
