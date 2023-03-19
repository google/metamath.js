include "ex.mm"
include "e10.mm"

theorem e10an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume e10an.1: |- (. ph ->. ps ).
  assume e10an.2: |- ch
  assume e10an.3: |- ( ( ps /\ ch ) -> th )


  assert |- (. ph ->. th ).

  proof
    wph
    wps
    wch
    wth
    e10an.1
    e10an.2
    wps
    wch
    wth
    e10an.3
    ex
    e10
end
