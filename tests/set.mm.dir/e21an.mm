include "ex.mm"
include "e21.mm"

theorem e21an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e21an.1: |- (. ph ,. ps ->. ch ).
  assume e21an.2: |- (. ph ->. th ).
  assume e21an.3: |- ( ( ch /\ th ) -> ta )


  assert |- (. ph ,. ps ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e21an.1
    e21an.2
    wch
    wth
    wta
    e21an.3
    ex
    e21
end
