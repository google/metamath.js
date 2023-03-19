include "cba.mm"
include "cfv.mm"
include "cpv.mm"
include "crn.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cv.mm"
include "fveq2.mm"
include "rneqd.mm"
include "df-ba.mm"
include "fvex.mm"
include "rnex.mm"
include "fvmpt.mm"
include "wn.mm"
include "c0.mm"
include "rn0.mm"
include "eqcomi.mm"
include "fvprc.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "rneqi.mm"
include "3eqtr4i.mm"

theorem bafval
  let cU: class U
  let cG: class G
  let cX: class X
  let vu: setvar u
  assume bafval.1: |- X = ( BaseSet ` U )
  assume bafval.2: |- G = ( +v ` U )


  assert |- X = ran G

  proof
    cU
    cba
    cfv
    #
    cU
    cpv
    cfv
    #
    crn
    #
    cX
    cG
    crn
    cU
    cvv
    wcel
    #
    @0
    @2
    wceq
    vu
    cU
    vu
    cv
    #
    cpv
    cfv
    #
    crn
    @2
    cvv
    cba
    @4
    cU
    wceq
    @5
    @1
    @4
    cU
    cpv
    fveq2
    rneqd
    vu
    df-ba
    @1
    cU
    cpv
    fvex
    rnex
    fvmpt
    @3
    wn
    #
    c0
    c0
    crn
    #
    @0
    @2
    @7
    c0
    rn0
    eqcomi
    cU
    cba
    fvprc
    @6
    @1
    c0
    cU
    cpv
    fvprc
    rneqd
    3eqtr4a
    pm2.61i
    bafval.1
    cG
    @1
    bafval.2
    rneqi
    3eqtr4i
end
