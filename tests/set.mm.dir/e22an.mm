include "ex.mm"
include "e22.mm"

theorem e22an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e22an.1: |- (. ph ,. ps ->. ch ).
  assume e22an.2: |- (. ph ,. ps ->. th ).
  assume e22an.3: |- ( ( ch /\ th ) -> ta )


  assert |- (. ph ,. ps ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e22an.1
    e22an.2
    wch
    wth
    wta
    e22an.3
    ex
    e22
end
