include "id.mm"
include "anim12i.mm"

theorem anim1i
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume anim1i.1: |- ( ph -> ps )


  assert |- ( ( ph /\ ch ) -> ( ps /\ ch ) )

  proof
    wph
    wps
    wch
    wch
    anim1i.1
    wch
    id
    anim12i
end
