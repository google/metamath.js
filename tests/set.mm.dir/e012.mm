include "vd01.mm"
include "e112.mm"

theorem e012
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e012.1: |- ph
  assume e012.2: |- (. ps ->. ch ).
  assume e012.3: |- (. ps ,. th ->. ta ).
  assume e012.4: |- ( ph -> ( ch -> ( ta -> et ) ) )


  assert |- (. ps ,. th ->. et ).

  proof
    wps
    wph
    wch
    wth
    wta
    wet
    wph
    wps
    e012.1
    vd01
    e012.2
    e012.3
    e012.4
    e112
end
