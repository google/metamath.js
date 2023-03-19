include "wb.mm"
include "ex.mm"
include "pm5.32d.mm"

theorem pm5.32da
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume pm5.32da.1: |- ( ( ph /\ ps ) -> ( ch <-> th ) )


  assert |- ( ph -> ( ( ps /\ ch ) <-> ( ps /\ th ) ) )

  proof
    wph
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wb
    pm5.32da.1
    ex
    pm5.32d
end
