include "wi.mm"
include "ax-frege8.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege10
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph -> ( ps -> ch ) ) -> th ) -> ( ( ps -> ( ph -> ch ) ) -> th ) )

  proof
    wps
    wph
    wch
    wi
    wi
    #
    wph
    wps
    wch
    wi
    wi
    #
    wi
    @1
    wth
    wi
    @0
    wth
    wi
    wi
    wps
    wph
    wch
    ax-frege8
    @0
    @1
    wth
    frege9
    ax-mp
end
