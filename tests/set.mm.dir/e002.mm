include "vd02.mm"
include "e222.mm"

theorem e002
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e002.1: |- ph
  assume e002.2: |- ps
  assume e002.3: |- (. ch ,. th ->. ta ).
  assume e002.4: |- ( ph -> ( ps -> ( ta -> et ) ) )


  assert |- (. ch ,. th ->. et ).

  proof
    wch
    wth
    wph
    wps
    wta
    wet
    wph
    wch
    wth
    e002.1
    vd02
    wps
    wch
    wth
    e002.2
    vd02
    e002.3
    e002.4
    e222
end
