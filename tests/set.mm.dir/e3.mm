include "wi.mm"
include "a1i.mm"
include "e33.mm"

theorem e3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e3.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e3.2: |- ( th -> ta )


  assert |- (. ph ,. ps ,. ch ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wth
    wta
    e3.1
    e3.1
    wth
    wta
    wi
    wth
    e3.2
    a1i
    e33
end
