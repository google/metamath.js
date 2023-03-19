include "wi.mm"
include "ex.mm"
include "wn.mm"
include "pm2.61i.mm"

theorem pm2.61ian
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume pm2.61ian.1: |- ( ( ph /\ ps ) -> ch )
  assume pm2.61ian.2: |- ( ( -. ph /\ ps ) -> ch )


  assert |- ( ps -> ch )

  proof
    wph
    wps
    wch
    wi
    wph
    wps
    wch
    pm2.61ian.1
    ex
    wph
    wn
    wps
    wch
    pm2.61ian.2
    ex
    pm2.61i
end
