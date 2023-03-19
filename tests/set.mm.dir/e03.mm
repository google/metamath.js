include "vd03.mm"
include "e33.mm"

theorem e03
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e03.1: |- ph
  assume e03.2: |- (. ps ,. ch ,. th ->. ta ).
  assume e03.3: |- ( ph -> ( ta -> et ) )


  assert |- (. ps ,. ch ,. th ->. et ).

  proof
    wps
    wch
    wth
    wph
    wta
    wet
    wph
    wps
    wch
    wth
    e03.1
    vd03
    e03.2
    e03.3
    e33
end
