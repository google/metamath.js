include "wi.mm"
include "ax-frege8.mm"
include "frege16.mm"
include "ax-mp.mm"

theorem frege17
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ( ch -> th ) ) ) -> ( ps -> ( ch -> ( ph -> th ) ) ) )

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
    wps
    wph
    @0
    wi
    wi
    wi
    @1
    wps
    wch
    wph
    wth
    wi
    wi
    wi
    wi
    wph
    wps
    @0
    ax-frege8
    @1
    wps
    wph
    wch
    wth
    frege16
    ax-mp
end
