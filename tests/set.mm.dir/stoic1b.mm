include "ancoms.mm"
include "stoic1a.mm"

theorem stoic1b
  let wph: wff ph
  let wps: wff ps
  let wth: wff th
  assume stoic1.1: |- ( ( ph /\ ps ) -> th )


  assert |- ( ( ps /\ -. th ) -> -. ph )

  proof
    wps
    wph
    wth
    wph
    wps
    wth
    stoic1.1
    ancoms
    stoic1a
end
