include "jaob.mm"

theorem axio
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch


  assert |- ( ( ( ph \/ ch ) -> ps ) <-> ( ( ph -> ps ) /\ ( ch -> ps ) ) )

  proof
    wph
    wps
    wch
    jaob
end
