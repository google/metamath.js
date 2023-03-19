include "wa.mm"
include "simpr.mm"
include "ad2antrl.mm"

theorem simprlr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ch )

  proof
    wps
    wch
    wa
    wch
    wph
    wth
    wps
    wch
    simpr
    ad2antrl
end
