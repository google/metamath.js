include "cevl.mm"
include "co.mm"
include "ces.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cv.mm"
include "cbs.mm"
include "oveq12.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "adantl.mm"
include "fveq12d.mm"
include "df-evl.mm"
include "fvex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "0fv.mm"
include "reldmevls.mm"
include "ovprc.mm"
include "fveq1d.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem evlval
  let cB: class B
  let cQ: class Q
  let cR: class R
  let cI: class I
  let vi: setvar i
  let vr: setvar r
  assume evlval.q: |- Q = ( I eval R )
  assume evlval.b: |- B = ( Base ` R )


  assert |- Q = ( ( I evalSub R ) ` B )

  proof
    cQ
    cI
    cR
    cevl
    co
    #
    cB
    cI
    cR
    ces
    co
    #
    cfv
    #
    evlval.q
    cI
    cvv
    wcel
    cR
    cvv
    wcel
    wa
    #
    @0
    @2
    wceq
    vi
    vr
    cI
    cR
    cvv
    cvv
    vr
    cv
    #
    cbs
    cfv
    #
    vi
    cv
    #
    @4
    ces
    co
    #
    cfv
    #
    @2
    cevl
    @6
    cI
    wceq
    #
    @4
    cR
    wceq
    #
    wa
    @5
    cB
    @7
    @1
    @6
    cI
    @4
    cR
    ces
    oveq12
    @10
    @5
    cB
    wceq
    @9
    @10
    @5
    cR
    cbs
    cfv
    cB
    @4
    cR
    cbs
    fveq2
    evlval.b
    syl6eqr
    adantl
    fveq12d
    vi
    vr
    df-evl
    #
    cB
    @1
    fvex
    ovmpt2a
    @3
    wn
    #
    @0
    cB
    c0
    cfv
    #
    @2
    @12
    @0
    c0
    @13
    vi
    vr
    @8
    cevl
    cI
    cR
    cvv
    cvv
    @11
    mpt2ndm0
    cB
    0fv
    syl6eqr
    @12
    cB
    @1
    c0
    cI
    cR
    ces
    reldmevls
    ovprc
    fveq1d
    eqtr4d
    pm2.61i
    eqtri
end
