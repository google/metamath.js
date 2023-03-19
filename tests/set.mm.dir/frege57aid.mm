include "wb.mm"
include "wi.mm"
include "frege52aid.mm"
include "frege56aid.mm"
include "ax-mp.mm"

theorem frege57aid
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) -> ( ps -> ph ) )

  proof
    wps
    wph
    wb
    wps
    wph
    wi
    #
    wi
    wph
    wps
    wb
    @0
    wi
    wps
    wph
    frege52aid
    wps
    wph
    frege56aid
    ax-mp
end
