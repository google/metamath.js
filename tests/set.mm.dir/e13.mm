include "vd13.mm"
include "e33.mm"

theorem e13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e13.1: |- (. ph ->. ps ).
  assume e13.2: |- (. ph ,. ch ,. th ->. ta ).
  assume e13.3: |- ( ps -> ( ta -> et ) )


  assert |- (. ph ,. ch ,. th ->. et ).

  proof
    wph
    wch
    wth
    wps
    wta
    wet
    wph
    wps
    wch
    wth
    e13.1
    vd13
    e13.2
    e13.3
    e33
end
