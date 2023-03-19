include "ex.mm"
include "e13.mm"

theorem e13an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  assume e13an.1: |- (. ph ->. ps ).
  assume e13an.2: |- (. ph ,. ch ,. th ->. ta ).
  assume e13an.3: |- ( ( ps /\ ta ) -> et )


  assert |- (. ph ,. ch ,. th ->. et ).

  proof
    wph
    wps
    wch
    wth
    wta
    wet
    e13an.1
    e13an.2
    wps
    wta
    wet
    e13an.3
    ex
    e13
end
