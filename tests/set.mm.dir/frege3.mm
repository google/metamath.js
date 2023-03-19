include "wi.mm"
include "ax-frege2.mm"
include "ax-frege1.mm"
include "ax-mp.mm"

theorem frege3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ch -> ( ph -> ps ) ) -> ( ( ch -> ph ) -> ( ch -> ps ) ) ) )

  proof
    wch
    wph
    wps
    wi
    #
    wi
    wch
    wph
    wi
    wch
    wps
    wi
    wi
    wi
    #
    @0
    @1
    wi
    wch
    wph
    wps
    ax-frege2
    @1
    @0
    ax-frege1
    ax-mp
end
