include "wn.mm"
include "wif.mm"
include "wb.mm"
include "frege54cor0a.mm"
include "biimpri.mm"
include "imim2i.mm"

theorem frege55lem1a
  let wph: wff ph
  let wps: wff ps
  let wta: wff ta


  assert |- ( ( ta -> if- ( ps , ph , -. ph ) ) -> ( ta -> ( ps <-> ph ) ) )

  proof
    wps
    wph
    wph
    wn
    wif
    #
    wps
    wph
    wb
    #
    wta
    @1
    @0
    wph
    wps
    frege54cor0a
    biimpri
    imim2i
end
