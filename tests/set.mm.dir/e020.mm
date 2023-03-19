include "vd02.mm"
include "e222.mm"

theorem e020
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e020.1: |- ph
  assume e020.2: |- (. ps ,. ch ->. th ).
  assume e020.3: |- ta
  assume e020.4: |- ( ph -> ( th -> ( ta -> et ) ) )


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
    e020.1
    vd02
    e020.2
    wta
    wps
    wch
    e020.3
    vd02
    e020.4
    e222
end
