include "wb.mm"
include "wi.mm"
include "frege52aid.mm"
include "ax-frege8.mm"
include "ax-mp.mm"

theorem frege53aid
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ( ph <-> ps ) -> ps ) )

  proof
    wph
    wps
    wb
    #
    wph
    wps
    wi
    wi
    wph
    @0
    wps
    wi
    wi
    wph
    wps
    frege52aid
    @0
    wph
    wps
    ax-frege8
    ax-mp
end
