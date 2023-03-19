include "wnf.mm"
include "weq.mm"
include "wal.mm"
include "wn.mm"
include "adantr.mm"
include "nfabd2.mm"

theorem nfabd
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  assume nfabd.1: |- F/ y ph
  assume nfabd.2: |- ( ph -> F/ x ps )


  assert |- ( ph -> F/_ x { y | ps } )

  proof
    wph
    wps
    vx
    vy
    nfabd.1
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
    nfabd.2
    adantr
    nfabd2
end
