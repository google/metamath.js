include "wi.mm"
include "imim1.mm"
include "peirce.mm"
include "syl6.mm"

theorem looinv
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ( ph -> ps ) -> ps ) -> ( ( ps -> ph ) -> ph ) )

  proof
    wph
    wps
    wi
    #
    wps
    wi
    wps
    wph
    wi
    @0
    wph
    wi
    wph
    @0
    wps
    wph
    imim1
    wph
    wps
    peirce
    syl6
end
