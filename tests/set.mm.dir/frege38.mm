include "wn.mm"
include "wi.mm"
include "frege36.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege38
  let wph: wff ph
  let wps: wff ps


  assert |- ( -. ph -> ( ph -> ps ) )

  proof
    wph
    wph
    wn
    #
    wps
    wi
    wi
    @0
    wph
    wps
    wi
    wi
    wph
    wps
    frege36
    wph
    @0
    wps
    ax-frege8
    ax-mp
end
