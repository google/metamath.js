include "vd03.mm"
include "e33.mm"

theorem e30
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e30.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e30.2: |- ta
  assume e30.3: |- ( th -> ( ta -> et ) )


  assert |- (. ph ,. ps ,. ch ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e30.1
    wta
    wph
    wps
    wch
    e30.2
    vd03
    e30.3
    e33
end
