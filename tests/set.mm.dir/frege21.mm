include "wi.mm"
include "frege9.mm"
include "frege19.mm"
include "ax-mp.mm"

theorem frege21
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph -> ps ) -> ch ) -> ( ( ph -> th ) -> ( ( th -> ps ) -> ch ) ) )

  proof
    wph
    wth
    wi
    #
    wth
    wps
    wi
    #
    wph
    wps
    wi
    #
    wi
    wi
    @2
    wch
    wi
    @0
    @1
    wch
    wi
    wi
    wi
    wph
    wth
    wps
    frege9
    @0
    @1
    @2
    wch
    frege19
    ax-mp
end
