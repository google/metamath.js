include "vd12.mm"
include "e222.mm"

theorem e221
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e221.1: |- (. ph ,. ps ->. ch ).
  assume e221.2: |- (. ph ,. ps ->. th ).
  assume e221.3: |- (. ph ->. ta ).
  assume e221.4: |- ( ch -> ( th -> ( ta -> et ) ) )


  assert |- (. ph ,. ps ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e221.1
    e221.2
    wph
    wta
    wps
    e221.3
    vd12
    e221.4
    e222
end
