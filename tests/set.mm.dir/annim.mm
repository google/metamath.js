include "wi.mm"
include "wn.mm"
include "wa.mm"
include "iman.mm"
include "con2bii.mm"

theorem annim
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( ph /\ -. ps ) <-> -. ( ph -> ps ) )

  proof
    wph
    wps
    wi
    wph
    wps
    wn
    wa
    wph
    wps
    iman
    con2bii
end
