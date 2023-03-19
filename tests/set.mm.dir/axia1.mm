include "simpl.mm"

theorem axia1
  let wph: wff ph
  let wps: wff ps


  assert |- ( ( ph /\ ps ) -> ph )

  proof
    wph
    wps
    simpl
end
