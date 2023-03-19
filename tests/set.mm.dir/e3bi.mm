include "biimpi.mm"
include "e3.mm"

theorem e3bi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e3bi.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e3bi.2: |- ( th <-> ta )


  assert |- (. ph ,. ps ,. ch ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e3bi.1
    wth
    wta
    e3bi.2
    biimpi
    e3
end
