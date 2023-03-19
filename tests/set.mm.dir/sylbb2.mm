include "biimpri.mm"
include "sylbi.mm"

theorem sylbb2
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume sylbb2.1: |- ( ph <-> ps )
  assume sylbb2.2: |- ( ch <-> ps )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    sylbb2.1
    wch
    wps
    sylbb2.2
    biimpri
    sylbi
end
