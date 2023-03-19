include "3expa.mm"
include "anabss3.mm"

theorem 3anidm23
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 3anidm23.1: |- ( ( ph /\ ps /\ ps ) -> ch )


  assert |- ( ( ph /\ ps ) -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    wps
    wch
    3anidm23.1
    3expa
    anabss3
end
