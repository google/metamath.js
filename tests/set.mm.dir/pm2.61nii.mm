include "pm2.61d1.mm"
include "pm2.61i.mm"

theorem pm2.61nii
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.61nii.1: |- ( ph -> ( ps -> ch ) )
  assume pm2.61nii.2: |- ( -. ph -> ch )
  assume pm2.61nii.3: |- ( -. ps -> ch )


  assert |- ch

  proof
    wph
    wch
    wph
    wps
    wch
    pm2.61nii.1
    pm2.61nii.3
    pm2.61d1
    pm2.61nii.2
    pm2.61i
end
