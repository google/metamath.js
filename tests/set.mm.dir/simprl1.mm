include "w3a.mm"
include "wa.mm"
include "simpl1.mm"
include "adantl.mm"

theorem simprl1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ph )

  proof
    wph
    wps
    wch
    w3a
    wth
    wa
    wph
    wta
    wph
    wps
    wch
    wth
    simpl1
    adantl
end
