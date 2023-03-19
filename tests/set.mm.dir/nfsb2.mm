include "weq.mm"
include "wal.mm"
include "wn.mm"
include "wsb.mm"
include "nfna1.mm"
include "hbsb2.mm"
include "nf5d.mm"

theorem nfsb2
  param wph: wff ph
  param vx: setvar x
  param vy: setvar y


  assert |- ( -. A. x x = y -> F/ x [ y / x ] ph )

  proof
    vx
    vy
    weq
    #
    vx
    wal
    wn
    wph
    vx
    vy
    wsb
    vx
    @0
    vx
    nfna1
    wph
    vx
    vy
    hbsb2
    nf5d
end
