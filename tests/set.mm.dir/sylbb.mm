include "biimpi.mm"
include "sylbi.mm"

theorem sylbb
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume sylbb.1: |- ( ph <-> ps )
  assume sylbb.2: |- ( ps <-> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    sylbb.1
    wps
    wch
    sylbb.2
    biimpi
    sylbi
end
