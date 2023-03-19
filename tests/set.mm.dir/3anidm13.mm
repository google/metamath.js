include "3com23.mm"
include "3anidm12.mm"

theorem 3anidm13
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3anidm13.1: |- ( ( ph /\ ps /\ ph ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wph
    wch
    3anidm13.1
    3com23
    3anidm12
end
