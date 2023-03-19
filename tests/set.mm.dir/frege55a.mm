include "wn.mm"
include "wif.mm"
include "wb.mm"
include "wi.mm"
include "frege54cor1a.mm"
include "frege53a.mm"
include "ax-mp.mm"

theorem frege55a
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) -> if- ( ps , ph , -. ph ) )

  proof
    wph
    wph
    wph
    wn
    #
    wif
    wph
    wps
    wb
    wps
    wph
    @0
    wif
    wi
    wph
    frege54cor1a
    wph
    wps
    @0
    wph
    frege53a
    ax-mp
end
