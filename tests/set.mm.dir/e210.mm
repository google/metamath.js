include "vd01.mm"
include "e211.mm"

theorem e210
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e210.1: |- (. ph ,. ps ->. ch ).
  assume e210.2: |- (. ph ->. th ).
  assume e210.3: |- ta
  assume e210.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ps ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e210.1
    e210.2
    wta
    wph
    e210.3
    vd01
    e210.4
    e211
end
