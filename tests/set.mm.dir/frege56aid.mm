include "wb.mm"
include "wi.mm"
include "frege55aid.mm"
include "frege9.mm"
include "ax-mp.mm"

theorem frege56aid
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph <-> ps ) -> ( ph -> ps ) ) -> ( ( ps <-> ph ) -> ( ph -> ps ) ) )

  proof
    wps
    wph
    wb
    #
    wph
    wps
    wb
    #
    wi
    @1
    wph
    wps
    wi
    #
    wi
    @0
    @2
    wi
    wi
    wps
    wph
    frege55aid
    @0
    @1
    @2
    frege9
    ax-mp
end
