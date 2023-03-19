include "wb.mm"
include "bibi2d.mm"
include "bicom.mm"
include "3bitr4g.mm"

theorem bibi1d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume imbid.1: |- ( ph -> ( ps <-> ch ) )


  assert |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> th ) ) )

  proof
    wph
    wth
    wps
    wb
    wth
    wch
    wb
    wps
    wth
    wb
    wch
    wth
    wb
    wph
    wps
    wch
    wth
    imbid.1
    bibi2d
    wps
    wth
    bicom
    wch
    wth
    bicom
    3bitr4g
end
