include "orcoms.mm"
include "orcs.mm"

theorem olcs
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume olcs.1: |- ( ( ph \/ ps ) -> ch )


  assert |- ( ps -> ch )

  proof
    wps
    wph
    wch
    wph
    wps
    wch
    olcs.1
    orcoms
    orcs
end
