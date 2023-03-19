include "id.mm"
include "ad2antlr.mm"

theorem simplr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph /\ ps ) /\ ch ) -> ps )

  proof
    wps
    wps
    wph
    wch
    wps
    id
    ad2antlr
end
