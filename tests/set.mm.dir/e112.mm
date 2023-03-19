include "vd12.mm"
include "e222.mm"

theorem e112
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e112.1: |- (. ph ->. ps ).
  assume e112.2: |- (. ph ->. ch ).
  assume e112.3: |- (. ph ,. th ->. ta ).
  assume e112.4: |- ( ps -> ( ch -> ( ta -> et ) ) )


  assert |- (. ph ,. th ->. et ).

  proof
    wph
    wth
    wps
    wch
    wta
    wet
    wph
    wps
    wth
    e112.1
    vd12
    wph
    wch
    wth
    e112.2
    vd12
    e112.3
    e112.4
    e222
end
