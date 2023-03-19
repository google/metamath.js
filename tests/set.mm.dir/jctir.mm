include "a1i.mm"
include "jca.mm"

theorem jctir
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume jctil.1: |- ( ph -> ps )
  assume jctil.2: |- ch


  assert |- ( ph -> ( ps /\ ch ) )

  proof
    wph
    wps
    wch
    jctil.1
    wch
    wph
    jctil.2
    a1i
    jca
end
