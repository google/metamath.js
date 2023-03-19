include "wi.mm"
include "ax-frege1.mm"
include "frege4.mm"
include "ax-mp.mm"

theorem frege5
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) )

  proof
    wph
    wps
    wi
    #
    wch
    @0
    wi
    wi
    @0
    wch
    wph
    wi
    wch
    wps
    wi
    wi
    wi
    @0
    wch
    ax-frege1
    wph
    wps
    wch
    frege4
    ax-mp
end
