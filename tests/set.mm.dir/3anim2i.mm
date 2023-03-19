include "id.mm"
include "3anim123i.mm"

theorem 3anim2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3animi.1: |- ( ph -> ps )


  assert |- ( ( ch /\ ph /\ th ) -> ( ch /\ ps /\ th ) )

  proof
    wch
    wch
    wph
    wps
    wth
    wth
    wch
    id
    3animi.1
    wth
    id
    3anim123i
end
