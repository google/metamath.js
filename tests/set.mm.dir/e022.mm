include "vd02.mm"
include "e222.mm"

theorem e022
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e022.1: |- ph
  assume e022.2: |- (. ps ,. ch ->. th ).
  assume e022.3: |- (. ps ,. ch ->. ta ).
  assume e022.4: |- ( ph -> ( th -> ( ta -> et ) ) )


  assert |- (. ps ,. ch ->. et ).

  proof
    wps
    wch
    wph
    wth
    wta
    wet
    wph
    wps
    wch
    e022.1
    vd02
    e022.2
    e022.3
    e022.4
    e222
end
