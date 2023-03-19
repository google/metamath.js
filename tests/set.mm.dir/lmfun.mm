include "cha.mm"
include "wcel.mm"
include "clm.mm"
include "cfv.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "weq.mm"
include "wi.mm"
include "wal.mm"
include "wfun.mm"
include "lmrel.mm"
include "a1i.mm"
include "simpl.mm"
include "simprl.mm"
include "simprr.mm"
include "lmmo.mm"
include "ex.mm"
include "alrimiv.mm"
include "dffun2.mm"
include "sylanbrc.mm"

theorem lmfun
  let cJ: class J
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( J e. Haus -> Fun ( ~~>t ` J ) )

  proof
    cJ
    cha
    wcel
    #
    cJ
    clm
    cfv
    #
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    @1
    wbr
    #
    @3
    vz
    cv
    #
    @1
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
    #
    vx
    wal
    @1
    wfun
    @2
    @0
    cJ
    lmrel
    a1i
    @0
    @12
    vx
    @0
    @11
    vy
    @0
    @10
    vz
    @0
    @8
    @9
    @0
    @8
    wa
    @4
    @6
    @3
    cJ
    @0
    @8
    simpl
    @0
    @5
    @7
    simprl
    @0
    @5
    @7
    simprr
    lmmo
    ex
    alrimiv
    alrimiv
    alrimiv
    vx
    vy
    vz
    @1
    dffun2
    sylanbrc
end
