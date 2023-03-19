include "vd02.mm"
include "e222.mm"

theorem e200
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e200.1: |- (. ph ,. ps ->. ch ).
  assume e200.2: |- th
  assume e200.3: |- ta
  assume e200.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ps ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e200.1
    wth
    wph
    wps
    e200.2
    vd02
    wta
    wph
    wps
    e200.3
    vd02
    e200.4
    e222
end
