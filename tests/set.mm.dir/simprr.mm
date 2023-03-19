include "id.mm"
include "ad2antll.mm"

theorem simprr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ph /\ ( ps /\ ch ) ) -> ch )

  proof
    wch
    wch
    wph
    wps
    wch
    id
    ad2antll
end
