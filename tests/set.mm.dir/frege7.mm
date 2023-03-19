include "wi.mm"
include "frege5.mm"
include "frege6.mm"
include "ax-mp.mm"

theorem frege7
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph -> ps ) -> ( ( ch -> ( th -> ph ) ) -> ( ch -> ( th -> ps ) ) ) )

  proof
    wph
    wps
    wi
    #
    wth
    wph
    wi
    #
    wth
    wps
    wi
    #
    wi
    wi
    @0
    wch
    @1
    wi
    wch
    @2
    wi
    wi
    wi
    wph
    wps
    wth
    frege5
    @0
    @1
    @2
    wch
    frege6
    ax-mp
end
