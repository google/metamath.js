include "biimpri.mm"
include "syl.mm"

theorem sylibr
  param wph: wff ph
  param wps: wff ps
  param wch: wff ch
  assume sylibr.1: |- ( ph -> ps )
  assume sylibr.2: |- ( ch <-> ps )


  assert |- ( ph -> ch )

  proof
    wph
    wps
    wch
    sylibr.1
    wch
    wps
    sylibr.2
    biimpri
    syl
end
