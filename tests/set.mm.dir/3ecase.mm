include "wi.mm"
include "3exp.mm"
include "wn.mm"
include "2a1d.mm"
include "pm2.61i.mm"
include "pm2.61nii.mm"

theorem 3ecase
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume 3ecase.1: |- ( -. ph -> th )
  assume 3ecase.2: |- ( -. ps -> th )
  assume 3ecase.3: |- ( -. ch -> th )
  assume 3ecase.4: |- ( ( ph /\ ps /\ ch ) -> th )


  assert |- th

  proof
    wps
    wch
    wth
    wph
    wps
    wch
    wth
    wi
    wi
    wph
    wps
    wch
    wth
    3ecase.4
    3exp
    wph
    wn
    wth
    wps
    wch
    3ecase.1
    2a1d
    pm2.61i
    3ecase.2
    3ecase.3
    pm2.61nii
end
