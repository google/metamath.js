include "wo.mm"
include "idd.mm"
include "wa.mm"
include "pm2.21d.mm"
include "mpand.mm"
include "jaod.mm"
include "mpjaod.mm"

theorem ecase2d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  assume ecase2d.1: |- ( ph -> ps )
  assume ecase2d.2: |- ( ph -> -. ( ps /\ ch ) )
  assume ecase2d.3: |- ( ph -> -. ( ps /\ th ) )
  assume ecase2d.4: |- ( ph -> ( ta \/ ( ch \/ th ) ) )


  assert |- ( ph -> ta )

  proof
    wph
    wta
    wta
    wch
    wth
    wo
    wph
    wta
    idd
    wph
    wch
    wta
    wth
    wph
    wps
    wch
    wta
    ecase2d.1
    wph
    wps
    wch
    wa
    wta
    ecase2d.2
    pm2.21d
    mpand
    wph
    wps
    wth
    wta
    ecase2d.1
    wph
    wps
    wth
    wa
    wta
    ecase2d.3
    pm2.21d
    mpand
    jaod
    ecase2d.4
    mpjaod
end
