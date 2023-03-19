include "vd23.mm"
include "e33.mm"

theorem e32
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e32.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e32.2: |- (. ph ,. ps ->. ta ).
  assume e32.3: |- ( th -> ( ta -> et ) )


  assert |- (. ph ,. ps ,. ch ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e32.1
    wph
    wps
    wta
    wch
    e32.2
    vd23
    e32.3
    e33
end
