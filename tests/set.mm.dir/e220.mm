include "vd02.mm"
include "e222.mm"

theorem e220
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e220.1: |- (. ph ,. ps ->. ch ).
  assume e220.2: |- (. ph ,. ps ->. th ).
  assume e220.3: |- ta
  assume e220.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ps ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e220.1
    e220.2
    wta
    wph
    wps
    e220.3
    vd02
    e220.4
    e222
end
