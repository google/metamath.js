include "cxr.mm"
include "wcel.mm"
include "csgn.mm"
include "cfv.mm"
include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "sgn0.mm"
include "syl6eq.mm"
include "c0ex.mm"
include "tpid2.mm"
include "syl6eqel.mm"
include "wne.mm"
include "clt.mm"
include "wbr.mm"
include "sgnn.mm"
include "negex.mm"
include "tpid1.mm"
include "adantlr.mm"
include "sgnp.mm"
include "1ex.mm"
include "tpid3.mm"
include "wo.mm"
include "0xr.mm"
include "xrlttri2.mm"
include "biimpa.mm"
include "mpanl2.mm"
include "mpjaodan.mm"
include "pm2.61dane.mm"

theorem sgncl
  let cA: class A


  assert |- ( A e. RR* -> ( sgn ` A ) e. { -u 1 , 0 , 1 } )

  proof
    cA
    cxr
    wcel
    #
    cA
    csgn
    cfv
    #
    c1
    cneg
    #
    cc0
    c1
    ctp
    #
    wcel
    #
    cA
    cc0
    @0
    cA
    cc0
    wceq
    #
    wa
    #
    @1
    cc0
    @3
    @6
    @1
    cc0
    csgn
    cfv
    cc0
    @6
    cA
    cc0
    csgn
    @0
    @5
    simpr
    fveq2d
    sgn0
    syl6eq
    @2
    cc0
    c1
    c0ex
    tpid2
    syl6eqel
    @0
    cA
    cc0
    wne
    #
    wa
    cA
    cc0
    clt
    wbr
    #
    @4
    cc0
    cA
    clt
    wbr
    #
    @0
    @8
    @4
    @7
    @0
    @8
    wa
    @1
    @2
    @3
    cA
    sgnn
    @2
    cc0
    c1
    c1
    negex
    tpid1
    syl6eqel
    adantlr
    @0
    @9
    @4
    @7
    @0
    @9
    wa
    @1
    c1
    @3
    cA
    sgnp
    @2
    cc0
    c1
    1ex
    tpid3
    syl6eqel
    adantlr
    @0
    cc0
    cxr
    wcel
    #
    @7
    @8
    @9
    wo
    #
    0xr
    @0
    @10
    wa
    @7
    @11
    cA
    cc0
    xrlttri2
    biimpa
    mpanl2
    mpjaodan
    pm2.61dane
end
