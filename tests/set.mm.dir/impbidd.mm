include "wi.mm"
include "wb.mm"
include "impbi.mm"
include "syl6c.mm"

theorem impbidd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume impbidd.1: |- ( ph -> ( ps -> ( ch -> th ) ) )
  assume impbidd.2: |- ( ph -> ( ps -> ( th -> ch ) ) )


  assert |- ( ph -> ( ps -> ( ch <-> th ) ) )

  proof
    wph
    wps
    wch
    wth
    wi
    wth
    wch
    wi
    wch
    wth
    wb
    impbidd.1
    impbidd.2
    wch
    wth
    impbi
    syl6c
end
