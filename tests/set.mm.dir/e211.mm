include "vd12.mm"
include "e222.mm"

theorem e211
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e211.1: |- (. ph ,. ps ->. ch ).
  assume e211.2: |- (. ph ->. th ).
  assume e211.3: |- (. ph ->. ta ).
  assume e211.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ps ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e211.1
    wph
    wth
    wps
    e211.2
    vd12
    wph
    wta
    wps
    e211.3
    vd12
    e211.4
    e222
end
