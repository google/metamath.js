include "id.mm"
include "jca.mm"

theorem ancli
  let wph: wff ph
  let wps: wff ps
  assume ancli.1: |- ( ph -> ps )


  assert |- ( ph -> ( ph /\ ps ) )

  proof
    wph
    wph
    wps
    wph
    id
    ancli.1
    jca
end
