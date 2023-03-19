include "id.mm"
include "3anim123i.mm"

theorem 3anim3i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3animi.1: |- ( ph -> ps )


  assert |- ( ( ch /\ th /\ ph ) -> ( ch /\ th /\ ps ) )

  proof
    wch
    wch
    wth
    wth
    wph
    wps
    wch
    id
    wth
    id
    3animi.1
    3anim123i
end
