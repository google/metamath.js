include "wi.mm"
include "ax-frege1.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege11
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph -> ps ) -> ch ) -> ( ps -> ch ) )

  proof
    wps
    wph
    wps
    wi
    #
    wi
    @0
    wch
    wi
    wps
    wch
    wi
    wi
    wps
    wph
    ax-frege1
    wps
    @0
    wch
    frege9
    ax-mp
end
