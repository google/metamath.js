include "wxo.mm"
include "wa.mm"
include "wn.mm"
include "wnan.mm"
include "xornan.mm"
include "df-nan.mm"
include "sylibr.mm"

theorem xornan2
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph \/_ ps ) -> ( ph -/\ ps ) )

  proof
    wph
    wps
    wxo
    wph
    wps
    wa
    wn
    wph
    wps
    wnan
    wph
    wps
    xornan
    wph
    wps
    df-nan
    sylibr
end
