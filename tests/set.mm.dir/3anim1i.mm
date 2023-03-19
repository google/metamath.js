include "id.mm"
include "3anim123i.mm"

theorem 3anim1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3animi.1: |- ( ph -> ps )


  assert |- ( ( ph /\ ch /\ th ) -> ( ps /\ ch /\ th ) )

  proof
    wph
    wps
    wch
    wch
    wth
    wth
    3animi.1
    wch
    id
    wth
    id
    3anim123i
end
