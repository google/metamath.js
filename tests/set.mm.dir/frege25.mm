include "wi.mm"
include "frege24.mm"
include "frege5.mm"
include "ax-mp.mm"

theorem frege25
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ph -> ( ps -> ( th -> ch ) ) ) )

  proof
    wps
    wch
    wi
    #
    wps
    wth
    wch
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
    frege24
    @0
    @1
    wph
    frege5
    ax-mp
end
