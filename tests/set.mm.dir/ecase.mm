include "ex.mm"
include "pm2.61nii.mm"

theorem ecase
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume ecase.1: |- ( -. ph -> ch )
  assume ecase.2: |- ( -. ps -> ch )
  assume ecase.3: |- ( ( ph /\ ps ) -> ch )


  assert |- ch

  proof
    wph
    wps
    wch
    wph
    wps
    wch
    ecase.3
    ex
    ecase.1
    ecase.2
    pm2.61nii
end
