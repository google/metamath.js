include "pm2.61ian.mm"
include "wn.mm"
include "pm2.61i.mm"

theorem 4cases
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume 4cases.1: |- ( ( ph /\ ps ) -> ch )
  assume 4cases.2: |- ( ( ph /\ -. ps ) -> ch )
  assume 4cases.3: |- ( ( -. ph /\ ps ) -> ch )
  assume 4cases.4: |- ( ( -. ph /\ -. ps ) -> ch )


  assert |- ch

  proof
    wps
    wch
    wph
    wps
    wch
    4cases.1
    4cases.3
    pm2.61ian
    wph
    wps
    wn
    wch
    4cases.2
    4cases.4
    pm2.61ian
    pm2.61i
end
