include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "cdif.mm"
include "wfun.mm"
include "reldif.mm"
include "wn.mm"
include "brdif.mm"
include "pm2.27.mm"
include "ad2ant2r.mm"
include "syl2anb.mm"
include "com12.mm"
include "alimi.mm"
include "2alimi.mm"
include "anim12i.mm"
include "dffun2.mm"
include "3imtr4i.mm"

theorem fundif
  let cA: class A
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( Fun F -> Fun ( F \ A ) )

  proof
    cF
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cF
    wbr
    #
    @1
    vz
    cv
    #
    cF
    wbr
    #
    wa
    #
    vy
    vz
    weq
    #
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    wa
    cF
    cA
    cdif
    #
    wrel
    #
    @1
    @2
    @11
    wbr
    #
    @1
    @4
    @11
    wbr
    #
    wa
    #
    @7
    wi
    #
    vz
    wal
    #
    vy
    wal
    vx
    wal
    #
    wa
    cF
    wfun
    @11
    wfun
    @0
    @12
    @10
    @18
    cF
    cA
    reldif
    @9
    @17
    vx
    vy
    @8
    @16
    vz
    @15
    @8
    @7
    @13
    @3
    @1
    @2
    cA
    wbr
    wn
    #
    wa
    @5
    @1
    @4
    cA
    wbr
    wn
    #
    wa
    @8
    @7
    wi
    #
    @14
    @1
    @2
    cF
    cA
    brdif
    @1
    @4
    cF
    cA
    brdif
    @3
    @5
    @21
    @19
    @20
    @6
    @7
    pm2.27
    ad2ant2r
    syl2anb
    com12
    alimi
    2alimi
    anim12i
    vx
    vy
    vz
    cF
    dffun2
    vx
    vy
    vz
    @11
    dffun2
    3imtr4i
end
