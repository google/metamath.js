include "wo.mm"
include "pm1.5.mm"
include "impbii.mm"

theorem or12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph \/ ( ps \/ ch ) ) <-> ( ps \/ ( ph \/ ch ) ) )

  proof
    wph
    wps
    wch
    wo
    wo
    wps
    wph
    wch
    wo
    wo
    wph
    wps
    wch
    pm1.5
    wps
    wph
    wch
    pm1.5
    impbii
end
