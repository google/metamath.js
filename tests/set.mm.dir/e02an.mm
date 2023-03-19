include "ex.mm"
include "e02.mm"

theorem e02an
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume e02an.1: |- ph
  assume e02an.2: |- (. ps ,. ch ->. th ).
  assume e02an.3: |- ( ( ph /\ th ) -> ta )


  assert |- (. ps ,. ch ->. ta ).

  proof
    wph
    wps
    wch
    wth
    wta
    e02an.1
    e02an.2
    wph
    wth
    wta
    e02an.3
    ex
    e02
end
