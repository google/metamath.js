include "biimpi.mm"
include "sylbi.mm"

theorem sylbb
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
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
