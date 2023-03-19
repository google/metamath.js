include "wb.mm"
include "biimpr.mm"
include "impcom.mm"

theorem bianir
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ( ps <-> ph ) ) -> ps )

  proof
    wps
    wph
    wb
    wph
    wps
    wps
    wph
    biimpr
    impcom
end
