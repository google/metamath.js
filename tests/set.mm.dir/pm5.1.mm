include "wb.mm"
include "pm5.501.mm"
include "biimpa.mm"

theorem pm5.1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ps ) -> ( ph <-> ps ) )

  proof
    wph
    wps
    wph
    wps
    wb
    wph
    wps
    pm5.501
    biimpa
end
