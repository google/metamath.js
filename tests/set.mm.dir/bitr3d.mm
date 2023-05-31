include "bicomd.mm"
include "bitrd.mm"

theorem bitr3d
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  param wth: wff th
  assume bitr3d.1: |- ( ph -> ( ps <-> ch ) )
  assume bitr3d.2: |- ( ph -> ( ps <-> th ) )


  assert |- ( ph -> ( ch <-> th ) )

  proof
    wph
    wch
    wps
    wth
    wph
    wps
    wch
    bitr3d.1
    bicomd
    bitr3d.2
    bitrd
end
