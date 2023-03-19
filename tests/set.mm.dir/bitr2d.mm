include "bitrd.mm"
include "bicomd.mm"

theorem bitr2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bitr2d.1: |- ( ph -> ( ps <-> ch ) )
  assume bitr2d.2: |- ( ph -> ( ch <-> th ) )


  assert |- ( ph -> ( th <-> ps ) )

  proof
    wph
    wps
    wth
    wph
    wps
    wch
    wth
    bitr2d.1
    bitr2d.2
    bitrd
    bicomd
end
