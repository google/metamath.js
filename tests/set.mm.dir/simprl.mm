include "id.mm"
include "ad2antrl.mm"

theorem simprl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ( ps /\ ch ) ) -> ps )

  proof
    wps
    wps
    wph
    wch
    wps
    id
    ad2antrl
end
