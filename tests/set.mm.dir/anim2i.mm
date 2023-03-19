include "id.mm"
include "anim12i.mm"

theorem anim2i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anim1i.1: |- ( ph -> ps )


  assert |- ( ( ch /\ ph ) -> ( ch /\ ps ) )

  proof
    wch
    wch
    wph
    wps
    wch
    id
    anim1i.1
    anim12i
end
