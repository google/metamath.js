include "wn.mm"
include "wi.mm"
include "frege43.mm"
include "frege21.mm"
include "ax-mp.mm"

theorem frege44
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> ps ) -> ( ( ps -> ph ) -> ph ) )

  proof
    wph
    wn
    #
    wph
    wi
    wph
    wi
    @0
    wps
    wi
    wps
    wph
    wi
    wph
    wi
    wi
    wph
    frege43
    @0
    wph
    wph
    wps
    frege21
    ax-mp
end
