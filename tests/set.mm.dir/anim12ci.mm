include "wa.mm"
include "anim12i.mm"
include "ancoms.mm"

theorem anim12ci
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume anim12i.1: |- ( ph -> ps )
  assume anim12i.2: |- ( ch -> th )


  assert |- ( ( ph /\ ch ) -> ( th /\ ps ) )

  proof
    wch
    wph
    wth
    wps
    wa
    wch
    wth
    wph
    wps
    anim12i.2
    anim12i.1
    anim12i
    ancoms
end
