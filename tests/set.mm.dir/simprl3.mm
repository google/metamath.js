include "w3a.mm"
include "wa.mm"
include "simpl3.mm"
include "adantl.mm"

theorem simprl3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ch )

  proof
    wph
    wps
    wch
    w3a
    wth
    wa
    wch
    wta
    wph
    wps
    wch
    wth
    simpl3
    adantl
end
