include "wn.mm"
include "wi.mm"
include "frege44.mm"
include "frege5.mm"
include "ax-mp.mm"

theorem frege45
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( -. ph -> ps ) -> ( -. ps -> ph ) ) -> ( ( -. ph -> ps ) -> ( ( ph -> ps ) -> ps ) ) )

  proof
    wps
    wn
    wph
    wi
    #
    wph
    wps
    wi
    wps
    wi
    #
    wi
    wph
    wn
    wps
    wi
    #
    @0
    wi
    @2
    @1
    wi
    wi
    wps
    wph
    frege44
    @0
    @1
    @2
    frege5
    ax-mp
end
