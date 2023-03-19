include "vd01.mm"
include "e111.mm"

theorem e001
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e001.1: |- ph
  assume e001.2: |- ps
  assume e001.3: |- (. ch ->. th ).
  assume e001.4: |- ( ph -> ( ps -> ( th -> ta ) ) )


  assert |- (. ch ->. ta ).

  proof
    wch
    wph
    wps
    wth
    wta
    wph
    wch
    e001.1
    vd01
    wps
    wch
    e001.2
    vd01
    e001.3
    e001.4
    e111
end
