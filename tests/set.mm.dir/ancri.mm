include "id.mm"
include "jca.mm"

theorem ancri
  let wph: wff ph
  let wps: wff ps
  assume ancri.1: |- ( ph -> ps )


  assert |- ( ph -> ( ps /\ ph ) )

  proof
    wph
    wps
    wph
    ancri.1
    wph
    id
    jca
end
