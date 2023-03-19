include "biimpi.mm"
include "syl.mm"

theorem sylbi
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume sylbi.1: |- ( ph <-> ps )
  assume sylbi.2: |- ( ps -> ch )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    wph
    wps
    sylbi.1
    biimpi
    sylbi.2
    syl
end
