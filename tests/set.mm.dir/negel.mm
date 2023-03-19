include "wa.mm"
include "adantl.mm"
include "wn.mm"
include "adantr.mm"
include "pm2.21fal.mm"

theorem negel
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  assume negel.1: |- ( ps -> ch )
  assume negel.2: |- ( ph -> -. ch )


  assert |- ( ( ph /\ ps ) -> F. )

  proof
    wph
    wps
    wa
    wch
    wps
    wch
    wph
    negel.1
    adantl
    wph
    wch
    wn
    wps
    negel.2
    adantr
    pm2.21fal
end
