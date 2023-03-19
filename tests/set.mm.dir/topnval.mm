include "cvv.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "ctopn.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cts.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq12d.mm"
include "df-topn.mm"
include "ovex.mm"
include "fvmpt.mm"
include "eqcomd.mm"
include "wn.mm"
include "c0.mm"
include "0rest.mm"
include "fvprc.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem topnval
  let cB: class B
  let cJ: class J
  let cW: class W
  let vw: setvar w
  assume topnval.1: |- B = ( Base ` W )
  assume topnval.2: |- J = ( TopSet ` W )


  assert |- ( J |`t B ) = ( TopOpen ` W )

  proof
    cW
    cvv
    wcel
    #
    cJ
    cB
    crest
    co
    #
    cW
    ctopn
    cfv
    #
    wceq
    @0
    @2
    @1
    vw
    cW
    vw
    cv
    #
    cts
    cfv
    #
    @3
    cbs
    cfv
    #
    crest
    co
    @1
    cvv
    ctopn
    @3
    cW
    wceq
    #
    @4
    cJ
    @5
    cB
    crest
    @6
    @4
    cW
    cts
    cfv
    #
    cJ
    @3
    cW
    cts
    fveq2
    topnval.2
    syl6eqr
    @6
    @5
    cW
    cbs
    cfv
    cB
    @3
    cW
    cbs
    fveq2
    topnval.1
    syl6eqr
    oveq12d
    vw
    df-topn
    cJ
    cB
    crest
    ovex
    fvmpt
    eqcomd
    @0
    wn
    #
    c0
    cB
    crest
    co
    c0
    @1
    @2
    cB
    0rest
    @8
    cJ
    c0
    cB
    crest
    @8
    cJ
    @7
    c0
    topnval.2
    cW
    cts
    fvprc
    syl5eq
    oveq1d
    cW
    ctopn
    fvprc
    3eqtr4a
    pm2.61i
end
