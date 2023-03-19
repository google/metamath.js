include "wo.mm"
include "jaod.mm"
include "pm2.61d.mm"

theorem ecase3d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  assume ecase3d.1: |- ( ph -> ( ps -> th ) )
  assume ecase3d.2: |- ( ph -> ( ch -> th ) )
  assume ecase3d.3: |- ( ph -> ( -. ( ps \/ ch ) -> th ) )


  assert |- ( ph -> th )

  proof
    wph
    wps
    wch
    wo
    wth
    wph
    wps
    wth
    wch
    ecase3d.1
    ecase3d.2
    jaod
    ecase3d.3
    pm2.61d
end
