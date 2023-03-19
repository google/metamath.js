include "ex.mm"
include "e31.mm"

theorem e31an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e31an.1: |- (. ph ,. ps ,. ch ->. th ).
  assume e31an.2: |- (. ph ->. ta ).
  assume e31an.3: |- ( ( th /\ ta ) -> et )


  assert |- (. ph ,. ps ,. ch ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e31an.1
    e31an.2
    wth
    wta
    wet
    e31an.3
    ex
    e31
end
