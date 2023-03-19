include "biimpri.mm"
include "e3.mm"

theorem e3bir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e3bir.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e3bir.2: |- ( ta <-> th )


  assert |- (. ph ,. ps ,. ch ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e3bir.1
    wta
    wth
    e3bir.2
    biimpri
    e3
end
