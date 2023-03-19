include "ex.mm"
include "e32.mm"

theorem e32an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e32an.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e32an.2: |- (. ph ,. ps ->. ta ).
  assume e32an.3: |- ( ( th /\ ta ) -> et )


  assert |- (. ph ,. ps ,. ch ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e32an.1
    e32an.2
    wth
    wta
    wet
    e32an.3
    ex
    e32
end
