include "vd13.mm"
include "e33.mm"

theorem e31
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e31.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e31.2: |- (. ph ->. ta ).
  assume e31.3: |- ( th -> ( ta -> et ) )


  assert |- (. ph ,. ps ,. ch ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e31.1
    wph
    wta
    wps
    wch
    e31.2
    vd13
    e31.3
    e33
end
