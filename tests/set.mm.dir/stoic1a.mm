include "ex.mm"
include "con3dimp.mm"

theorem stoic1a
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  assume stoic1.1: |- ( ( ph /\ ps ) -> th )


  assert |- ( ( ph /\ -. th ) -> -. ps )

  proof
    wph
    wps
    wth
    wph
    wps
    wth
    stoic1.1
    ex
    con3dimp
end
