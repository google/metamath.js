include "wb.mm"
include "a1d.mm"
include "pm5.74d.mm"

theorem imbi2d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume imbid.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( th -> ps ) <-> ( th -> ch ) ) )

  proof
    wph
    wth
    wps
    wch
    wph
    wps
    wch
    wb
    wth
    imbid.1
    a1d
    pm5.74d
end
