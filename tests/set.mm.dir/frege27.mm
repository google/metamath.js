include "wi.mm"
include "ax-frege1.mm"
include "frege26.mm"
include "ax-mp.mm"

theorem frege27
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ph )

  proof
    wph
    wps
    wph
    wi
    wi
    #
    wph
    wph
    wi
    wph
    wps
    ax-frege1
    @0
    wph
    frege26
    ax-mp
end
