include "wb.mm"
include "bibi1d.mm"
include "bibi2d.mm"
include "bitrd.mm"

theorem bibi12d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  param wta: wff ta
  assume imbi12d.1: |- ( ph -> ( ps <-> ch ) )
  assume imbi12d.2: |- ( ph -> ( th <-> ta ) )


  assert |- ( ph -> ( ( ps <-> th ) <-> ( ch <-> ta ) ) )

  proof
    wph
    wps
    wth
    wb
    wch
    wth
    wb
    wch
    wta
    wb
    wph
    wps
    wch
    wth
    imbi12d.1
    bibi1d
    wph
    wth
    wta
    wch
    imbi12d.2
    bibi2d
    bitrd
end
