include "wi.mm"
include "ax-frege8.mm"
include "frege5.mm"
include "ax-mp.mm"

theorem frege12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ( ch -> th ) ) ) -> ( ph -> ( ch -> ( ps -> th ) ) ) )

  proof
    wps
    wch
    wth
    wi
    wi
    #
    wch
    wps
    wth
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
    ax-frege8
    @0
    @1
    wph
    frege5
    ax-mp
end
