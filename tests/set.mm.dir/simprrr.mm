include "wa.mm"
include "simpr.mm"
include "ad2antll.mm"

theorem simprrr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ps /\ ( ch /\ th ) ) ) -> th )

  proof
    wch
    wth
    wa
    wth
    wph
    wps
    wch
    wth
    simpr
    ad2antll
end
