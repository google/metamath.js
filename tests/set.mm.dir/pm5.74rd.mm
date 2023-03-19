include "wi.mm"
include "wb.mm"
include "pm5.74.mm"
include "sylibr.mm"

theorem pm5.74rd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume pm5.74rd.1: |- ( ph -> ( ( ps -> ch ) <-> ( ps -> th ) ) )


  assert |- ( ph -> ( ps -> ( ch <-> th ) ) )

  proof
    wph
    wps
    wch
    wi
    wps
    wth
    wi
    wb
    wps
    wch
    wth
    wb
    wi
    pm5.74rd.1
    wps
    wch
    wth
    pm5.74
    sylibr
end
