include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "w3a.mm"
include "cbl.mm"
include "co.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "wa.mm"
include "blval.mm"
include "eleq2d.mm"
include "wceq.mm"
include "oveq2.mm"
include "breq1d.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem elbl
  let cA: class A
  let cD: class D
  let cP: class P
  let cR: class R
  let cX: class X
  let vx: setvar x
  let vr: setvar r
  let vy: setvar y
  let wph: wff ph
  let cQ: class Q
  let cS: class S


  assert |- ( ( D e. ( *Met ` X ) /\ P e. X /\ R e. RR* ) -> ( A e. ( P ( ball ` D ) R ) <-> ( A e. X /\ ( P D A ) < R ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    cP
    cX
    wcel
    cR
    cxr
    wcel
    w3a
    #
    cA
    cP
    cR
    cD
    cbl
    cfv
    co
    #
    wcel
    cA
    cP
    vx
    cv
    #
    cD
    co
    #
    cR
    clt
    wbr
    #
    vx
    cX
    crab
    #
    wcel
    cA
    cX
    wcel
    cP
    cA
    cD
    co
    #
    cR
    clt
    wbr
    #
    wa
    @0
    @1
    @5
    cA
    vx
    cD
    cP
    cR
    cX
    blval
    eleq2d
    @4
    @7
    vx
    cA
    cX
    @2
    cA
    wceq
    @3
    @6
    cR
    clt
    @2
    cA
    cP
    cD
    oveq2
    breq1d
    elrab
    syl6bb
end
