include "wo.mm"
include "jaoi.mm"
include "pm2.61i.mm"

theorem ecase3
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume ecase3.1: |- ( ph -> ch )
  assume ecase3.2: |- ( ps -> ch )
  assume ecase3.3: |- ( -. ( ph \/ ps ) -> ch )


  assert |- ch

  proof
    wph
    wps
    wo
    wch
    wph
    wch
    wps
    ecase3.1
    ecase3.2
    jaoi
    ecase3.3
    pm2.61i
end
