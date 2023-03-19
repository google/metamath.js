include "wn.mm"
include "wi.mm"
include "wo.mm"
include "pm2.54.mm"
include "syl.mm"

theorem orrd
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume orrd.1: |- ( ph -> ( -. ps -> ch ) )


  assert |- ( ph -> ( ps \/ ch ) )

  proof
    wph
    wps
    wn
    wch
    wi
    wps
    wch
    wo
    orrd.1
    wps
    wch
    pm2.54
    syl
end
