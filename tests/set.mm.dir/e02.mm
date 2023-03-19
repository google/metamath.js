include "vd02.mm"
include "e22.mm"

theorem e02
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e02.1: |- ph
  assume e02.2: |- (. ps ,. ch ->. th ).
  assume e02.3: |- ( ph -> ( th -> ta ) )


  assert |- (. ps ,. ch ->. ta ).

  proof
    wps
    wch
    wph
    wth
    wta
    wph
    wps
    wch
    e02.1
    vd02
    e02.2
    e02.3
    e22
end
