include "id.mm"
include "jaoi.mm"

theorem bj-jaoi2
  let wph: wff ph
  let wps: wff ps
  assume bj-jaoi1.1: |- ( ph -> ps )


  assert |- ( ( ps \/ ph ) -> ps )

  proof
    wps
    wps
    wph
    wps
    id
    bj-jaoi1.1
    jaoi
end
