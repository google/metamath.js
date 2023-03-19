include "ex.mm"
include "e03.mm"

theorem e03an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e03an.1: |- ph
  assume e03an.2: |- (. ps ,. ch ,. th ->. ta ).
  assume e03an.3: |- ( ( ph /\ ta ) -> et )


  assert |- (. ps ,. ch ,. th ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e03an.1
    e03an.2
    wph
    wta
    wet
    e03an.3
    ex
    e03
end
