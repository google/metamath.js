include "wi.mm"
include "wb.mm"
include "impbi.mm"
include "mp2.mm"

theorem impbii
  let wph: wff ph
  let wps: wff ps
  assume impbii.1: |- ( ph -> ps )
  assume impbii.2: |- ( ps -> ph )


  assert |- ( ph <-> ps )

  proof
    wph
    wps
    wi
    wps
    wph
    wi
    wph
    wps
    wb
    impbii.1
    impbii.2
    wph
    wps
    impbi
    mp2
end
