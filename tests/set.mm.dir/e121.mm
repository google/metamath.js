include "vd12.mm"
include "e222.mm"

theorem e121
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e121.1: |- (. ph ->. ps ).
  assume e121.2: |- (. ph ,. ch ->. th ).
  assume e121.3: |- (. ph ->. ta ).
  assume e121.4: |- ( ps -> ( th -> ( ta -> et ) ) )


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
    e121.1
    vd12
    e121.2
    wph
    wta
    wch
    e121.3
    vd12
    e121.4
    e222
end
