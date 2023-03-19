include "wb.mm"
include "wnan.mm"
include "nanbi1.mm"
include "nanbi2.mm"
include "sylan9bb.mm"

theorem nanbi12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ( ph <-> ps ) /\ ( ch <-> th ) ) -> ( ( ph -/\ ch ) <-> ( ps -/\ th ) ) )

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
    wth
    wb
    wps
    wth
    wnan
    wph
    wps
    wch
    nanbi1
    wch
    wth
    wps
    nanbi2
    sylan9bb
end
