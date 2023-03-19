include "vd23.mm"
include "e33.mm"

theorem e23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e23.1: |- (. ph ,. ps ->. ch ).
  assume e23.2: |- (. ph ,. ps ,. th ->. ta ).
  assume e23.3: |- ( ch -> ( ta -> et ) )


  assert |- (. ph ,. ps ,. th ->. et ).

  proof
    wph
    wps
    wth
    wch
    wta
    wet
    wph
    wps
    wch
    wth
    e23.1
    vd23
    e23.2
    e23.3
    e33
end
