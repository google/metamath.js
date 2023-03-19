include "wi.mm"
include "a1i.mm"
include "e333.mm"

theorem e33
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e33.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e33.2: |- (. ph ,. ps ,. ch ->. ta ).
  assume e33.3: |- ( th -> ( ta -> et ) )


  assert |- (. ph ,. ps ,. ch ->. et ).

  proof
    wph
    wps
    wch
    wth
    wth
    wta
    wet
    e33.1
    e33.1
    e33.2
    wth
    wta
    wet
    wi
    wi
    wth
    e33.3
    a1i
    e333
end
