include "wnan.mm"
include "wa.mm"
include "df-nan.mm"
include "con2bii.mm"

theorem nanan
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ps ) <-> -. ( ph -/\ ps ) )

  proof
    wph
    wps
    wnan
    wph
    wps
    wa
    wph
    wps
    df-nan
    con2bii
end
