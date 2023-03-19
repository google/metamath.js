include "3anidm13.mm"

theorem 3anidm12p1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3anidm12p1.1: |- ( ( ph /\ ps /\ ph ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    3anidm12p1.1
    3anidm13
end
