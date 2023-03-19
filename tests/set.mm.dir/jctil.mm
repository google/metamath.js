include "a1i.mm"
include "jca.mm"

theorem jctil
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume jctil.1: |- ( ph -> ps )
  assume jctil.2: |- ch


  assert |- ( ph -> ( ch /\ ps ) )

  proof
    wph
    wch
    wps
    wch
    wph
    jctil.2
    a1i
    jctil.1
    jca
end
