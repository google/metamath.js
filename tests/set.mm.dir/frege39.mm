include "wn.mm"
include "wi.mm"
include "frege38.mm"
include "ax-frege2.mm"
include "ax-mp.mm"

theorem frege39
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( -. ph -> ph ) -> ( -. ph -> ps ) )

  proof
    wph
    wn
    #
    wph
    wps
    wi
    wi
    @0
    wph
    wi
    @0
    wps
    wi
    wi
    wph
    wps
    frege38
    @0
    wph
    wps
    ax-frege2
    ax-mp
end
