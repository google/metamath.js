include "bicomd.mm"
include "bitrd.mm"

theorem bitr4d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume bitr4d.1: |- ( ph -> ( ps <-> ch ) )
  assume bitr4d.2: |- ( ph -> ( th <-> ch ) )


  assert |- ( ph -> ( ps <-> th ) )

  proof
    wph
    wps
    wch
    wth
    bitr4d.1
    wph
    wth
    wch
    bitr4d.2
    bicomd
    bitrd
end
