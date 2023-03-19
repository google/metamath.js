include "w3a.mm"
include "3anrot.mm"
include "sylbir.mm"
include "3anidm12.mm"

theorem 3anidm12p2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3anidm12p2.1: |- ( ( ps /\ ph /\ ph ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wph
    wps
    w3a
    wps
    wph
    wph
    w3a
    wch
    wps
    wph
    wph
    3anrot
    3anidm12p2.1
    sylbir
    3anidm12
end
