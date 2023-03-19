include "wa.mm"
include "simpl.mm"
include "ad2antll.mm"

theorem simprrl
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> ch )

  proof
    wch
    wth
    wa
    wch
    wph
    wps
    wch
    wth
    simpl
    ad2antll
end
