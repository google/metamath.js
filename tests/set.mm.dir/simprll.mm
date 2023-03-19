include "wa.mm"
include "simpl.mm"
include "ad2antrl.mm"

theorem simprll
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th


  assert |- ( ( ph /\ ( ( ps /\ ch ) /\ th ) ) -> ps )

  proof
    wps
    wch
    wa
    wps
    wph
    wth
    wps
    wch
    simpl
    ad2antrl
end
