include "wb.mm"
include "bicom.mm"
include "syl6ib.mm"

theorem bicomdd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bicomdd.1: |- ( ph -> ( ps -> ( ch <-> th ) ) )


  assert |- ( ph -> ( ps -> ( th <-> ch ) ) )

  proof
    wph
    wps
    wch
    wth
    wb
    wth
    wch
    wb
    bicomdd.1
    wch
    wth
    bicom
    syl6ib
end
