include "wb.mm"
include "wnan.mm"
include "nanbi1.mm"
include "nancom.mm"
include "3bitr4g.mm"

theorem nanbi2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph <-> ps ) -> ( ( ch -/\ ph ) <-> ( ch -/\ ps ) ) )

  proof
    wph
    wps
    wb
    wph
    wch
    wnan
    wps
    wch
    wnan
    wch
    wph
    wnan
    wch
    wps
    wnan
    wph
    wps
    wch
    nanbi1
    wch
    wph
    nancom
    wch
    wps
    nancom
    3bitr4g
end
