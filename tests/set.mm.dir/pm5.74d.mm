include "wb.mm"
include "wi.mm"
include "pm5.74.mm"
include "sylib.mm"

theorem pm5.74d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume pm5.74d.1: |- ( ph -> ( ps -> ( ch <-> th ) ) )


  assert |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) )

  proof
    wph
    wps
    wch
    wth
    wb
    wi
    wps
    wch
    wi
    wps
    wth
    wi
    wb
    pm5.74d.1
    wps
    wch
    wth
    pm5.74
    sylib
end
