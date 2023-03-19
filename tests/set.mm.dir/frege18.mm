include "wi.mm"
include "frege5.mm"
include "frege16.mm"
include "ax-mp.mm"

theorem frege18
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ( ps -> ch ) ) -> ( ( th -> ph ) -> ( ps -> ( th -> ch ) ) ) )

  proof
    wph
    wps
    wch
    wi
    #
    wi
    #
    wth
    wph
    wi
    #
    wth
    @0
    wi
    wi
    wi
    @1
    @2
    wps
    wth
    wch
    wi
    wi
    wi
    wi
    wph
    @0
    wth
    frege5
    @1
    @2
    wth
    wps
    wch
    frege16
    ax-mp
end
