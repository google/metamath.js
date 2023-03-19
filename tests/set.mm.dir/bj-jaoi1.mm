include "id.mm"
include "jaoi.mm"

theorem bj-jaoi1
  let wph: wff ph
  let wps: wff ps
  assume bj-jaoi1.1: |- ( ph -> ps )


  assert |- ( ( ph \/ ps ) -> ps )

  proof
    wph
    wps
    wps
    bj-jaoi1.1
    wps
    id
    jaoi
end
