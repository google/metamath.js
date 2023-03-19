include "wnf.mm"
include "weq.mm"
include "wal.mm"
include "wn.mm"
include "adantr.mm"
include "nfeud2.mm"

theorem nfeud
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume nfeud.1: |- F/ y ph
  assume nfeud.2: |- ( ph -> F/ x ps )


  assert |- ( ph -> F/ x E! y ps )

  proof
    wph
    wps
    vx
    vy
    nfeud.1
    wph
    wps
    vx
    wnf
    vx
    vy
    weq
    vx
    wal
    wn
    nfeud.2
    adantr
    nfeud2
end
