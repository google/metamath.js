include "wa.mm"
include "wn.mm"
include "wi.mm"
include "df-an.mm"
include "con2bii.mm"

theorem imnan
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( ph -> -. ps ) <-> -. ( ph /\ ps ) )

  proof
    wph
    wps
    wa
    wph
    wps
    wn
    wi
    wph
    wps
    df-an
    con2bii
end
