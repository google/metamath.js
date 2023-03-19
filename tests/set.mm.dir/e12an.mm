include "ex.mm"
include "e12.mm"

theorem e12an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e12an.1: |- (. ph ->. ps ).
  assume e12an.2: |- (. ph ,. ch ->. th ).
  assume e12an.3: |- ( ( ps /\ th ) -> ta )


  assert |- (. ph ,. ch ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e12an.1
    e12an.2
    wps
    wth
    wta
    e12an.3
    ex
    e12
end
