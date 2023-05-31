include "wo.mm"
include "pm1.4.mm"
include "impbii.mm"

theorem orcom
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( ph \/ ps ) <-> ( ps \/ ph ) )

  proof
    wph
    wps
    wo
    wps
    wph
    wo
    wph
    wps
    pm1.4
    wps
    wph
    pm1.4
    impbii
end
