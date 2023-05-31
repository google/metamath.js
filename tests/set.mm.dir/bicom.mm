include "wb.mm"
include "bicom1.mm"
include "impbii.mm"

theorem bicom
  param wph: wff ph
  param wps: wff ps


  assert |- ( ( ph <-> ps ) <-> ( ps <-> ph ) )

  proof
    wph
    wps
    wb
    wps
    wph
    wb
    wph
    wps
    bicom1
    wps
    wph
    bicom1
    impbii
end
