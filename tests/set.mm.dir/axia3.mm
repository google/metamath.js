include "pm3.2.mm"

theorem axia3
  let wph: wff ph
  let wps: wff ps


  assert |- ( ph -> ( ps -> ( ph /\ ps ) ) )

  proof
    wph
    wps
    pm3.2
end
