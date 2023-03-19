include "vd12.mm"
include "e222.mm"

theorem e212
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e212.1: |- (. ph ,. ps ->. ch ).
  assume e212.2: |- (. ph ->. th ).
  assume e212.3: |- (. ph ,. ps ->. ta ).
  assume e212.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ps ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e212.1
    wph
    wth
    wps
    e212.2
    vd12
    e212.3
    e212.4
    e222
end
