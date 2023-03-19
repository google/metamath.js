include "wi.mm"
include "frege5.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege9
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph -> ps ) -> ( ( ps -> ch ) -> ( ph -> ch ) ) )

  proof
    wps
    wch
    wi
    #
    wph
    wps
    wi
    #
    wph
    wch
    wi
    #
    wi
    wi
    @1
    @0
    @2
    wi
    wi
    wps
    wch
    wph
    frege5
    @0
    @1
    @2
    ax-frege8
    ax-mp
end
