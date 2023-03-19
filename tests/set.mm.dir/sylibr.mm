include "biimpri.mm"
include "syl.mm"

theorem sylibr
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
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
