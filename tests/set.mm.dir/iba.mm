include "wa.mm"
include "pm3.21.mm"
include "simpl.mm"
include "impbid1.mm"

theorem iba
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps <-> ( ps /\ ph ) ) )

  proof
    wph
    wps
    wps
    wph
    wa
    wph
    wps
    pm3.21
    wps
    wph
    simpl
    impbid1
end
