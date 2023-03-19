include "wb.mm"
include "pm5.501.mm"
include "pm5.74i.mm"

theorem ibib
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph -> ps ) <-> ( ph -> ( ph <-> ps ) ) )

  proof
    wph
    wps
    wph
    wps
    wb
    wph
    wps
    pm5.501
    pm5.74i
end
