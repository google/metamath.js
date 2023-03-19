include "biimpri.mm"
include "sylib.mm"

theorem sylbb1
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume sylbb1.1: |- ( ph <-> ps )
  assume sylbb1.2: |- ( ph <-> ch )


  assert |- ( ps -> ch )

  proof
    wps
    wph
    wch
    wph
    wps
    sylbb1.1
    biimpri
    sylbb1.2
    sylib
end
