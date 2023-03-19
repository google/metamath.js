include "w3a.mm"
include "wa.mm"
include "simpl2.mm"
include "adantl.mm"

theorem simprl2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta


  assert |- ( ( ta /\ ( ( ph /\ ps /\ ch ) /\ th ) ) -> ps )

  proof
    wph
    wps
    wch
    w3a
    wth
    wa
    wps
    wta
    wph
    wps
    wch
    wth
    simpl2
    adantl
end
