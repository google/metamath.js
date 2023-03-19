include "3expib.mm"
include "anabsi5.mm"

theorem 3anidm12
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3anidm12.1: |- ( ( ph /\ ph /\ ps ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wph
    wps
    wch
    3anidm12.1
    3expib
    anabsi5
end
