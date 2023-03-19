include "ex.mm"
include "e33.mm"

theorem e33an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e33an.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e33an.2: |- (. ph ,. ps ,. ch ->. ta ).
  assume e33an.3: |- ( ( th /\ ta ) -> et )


  assert |- (. ph ,. ps ,. ch ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e33an.1
    e33an.2
    wth
    wta
    wet
    e33an.3
    ex
    e33
end
