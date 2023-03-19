include "wb.mm"
include "wn.mm"
include "wif.mm"
include "wi.mm"
include "frege55a.mm"
include "frege55lem1a.mm"
include "ax-mp.mm"

theorem frege55cor1a
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) -> ( ps <-> ph ) )

  proof
    wph
    wps
    wb
    #
    wps
    wph
    wph
    wn
    wif
    wi
    @0
    wps
    wph
    wb
    wi
    wph
    wps
    frege55a
    wph
    wps
    @0
    frege55lem1a
    ax-mp
end
