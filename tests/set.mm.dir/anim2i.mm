include "id.mm"
include "anim12i.mm"

theorem anim2i
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
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
