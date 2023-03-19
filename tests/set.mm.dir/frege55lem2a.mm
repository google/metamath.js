include "wb.mm"
include "wn.mm"
include "wif.mm"
include "wi.mm"
include "bicom1.mm"
include "frege54cor0a.mm"
include "sylib.mm"
include "idi.mm"

theorem frege55lem2a
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph <-> ps ) -> if- ( ps , ph , -. ph ) )

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
    #
    wi
    @0
    wps
    wph
    wb
    @1
    wph
    wps
    bicom1
    wph
    wps
    frege54cor0a
    sylib
    idi
end
