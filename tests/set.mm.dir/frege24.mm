include "wi.mm"
include "ax-frege1.mm"
include "frege12.mm"
include "ax-mp.mm"

theorem frege24
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ph -> ( ch -> ps ) ) )

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
    wph
    wch
    wps
    wi
    wi
    wi
    @0
    wch
    ax-frege1
    @0
    wch
    wph
    wps
    frege12
    ax-mp
end
