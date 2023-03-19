include "vd12.mm"
include "e222.mm"

theorem e122
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e122.1: |- (. ph ->. ps ).
  assume e122.2: |- (. ph ,. ch ->. th ).
  assume e122.3: |- (. ph ,. ch ->. ta ).
  assume e122.4: |- ( ps -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ch ->. et ).

  proof
    wph
    wch
    wps
    wth
    wta
    wet
    wph
    wps
    wch
    e122.1
    vd12
    e122.2
    e122.3
    e122.4
    e222
end
