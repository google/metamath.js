include "ex.mm"
include "e30.mm"

theorem e30an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e30an.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e30an.2: |- ta
  assume e30an.3: |- ( ( th /\ ta ) -> et )


  assert |- (. ph ,. ps ,. ch ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e30an.1
    e30an.2
    wth
    wta
    wet
    e30an.3
    ex
    e30
end
