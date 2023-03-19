include "ex.mm"
include "e20.mm"

theorem e20an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e20an.1: |- (. ph ,. ps ->. ch ).
  assume e20an.2: |- th
  assume e20an.3: |- ( ( ch /\ th ) -> ta )


  assert |- (. ph ,. ps ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e20an.1
    e20an.2
    wch
    wth
    wta
    e20an.3
    ex
    e20
end
