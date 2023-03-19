include "biimpi.mm"
include "e2.mm"

theorem e2bi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume e2bi.1: |- (. ph ,. ps ->. ch ).
  assume e2bi.2: |- ( ch <-> th )


  assert |- (. ph ,. ps ->. th ).

  proof
    wph
    wps
    wch
    wth
    e2bi.1
    wch
    wth
    e2bi.2
    biimpi
    e2
end
