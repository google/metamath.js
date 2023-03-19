include "ex.mm"
include "e11.mm"

theorem e11an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume e11an.1: |- (. ph ->. ps ).
  assume e11an.2: |- (. ph ->. ch ).
  assume e11an.3: |- ( ( ps /\ ch ) -> th )


  assert |- (. ph ->. th ).

  proof
    wph
    wps
    wch
    wth
    e11an.1
    e11an.2
    wps
    wch
    wth
    e11an.3
    ex
    e11
end
