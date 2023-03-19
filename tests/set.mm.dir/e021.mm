include "vd01.mm"
include "e121.mm"

theorem e021
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e021.1: |- ph
  assume e021.2: |- (. ps ,. ch ->. th ).
  assume e021.3: |- (. ps ->. ta ).
  assume e021.4: |- ( ph -> ( th -> ( ta -> et ) ) )


  assert |- (. ps ,. ch ->. et ).

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wph
    wps
    e021.1
    vd01
    e021.2
    e021.3
    e021.4
    e121
end
