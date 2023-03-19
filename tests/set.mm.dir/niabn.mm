include "wa.mm"
include "wn.mm"
include "simpr.mm"
include "pm2.24i.mm"
include "pm5.21ni.mm"

theorem niabn
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume niabn.1: |- ph


  assert |- ( -. ps -> ( ( ch /\ ps ) <-> -. ph ) )

  proof
    wch
    wps
    wa
    wps
    wph
    wn
    wch
    wps
    simpr
    wph
    wps
    niabn.1
    pm2.24i
    pm5.21ni
end
