include "ex.mm"
include "e23.mm"

theorem e23an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e23an.1: |- (. ph ,. ps ->. ch ).
  assume e23an.2: |- (. ph ,. ps ,. th ->. ta ).
  assume e23an.3: |- ( ( ch /\ ta ) -> et )


  assert |- (. ph ,. ps ,. th ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e23an.1
    e23an.2
    wch
    wta
    wet
    e23an.3
    ex
    e23
end
