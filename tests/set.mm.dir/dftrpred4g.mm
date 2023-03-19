include "wcel.mm"
include "wse.mm"
include "wa.mm"
include "ctrpred.mm"
include "cpred.mm"
include "cv.mm"
include "ciun.mm"
include "cun.mm"
include "csn.mm"
include "dftrpred3g.mm"
include "iunun.mm"
include "iunid.mm"
include "uneq1i.mm"
include "eqtri.mm"
include "syl6eqr.mm"

theorem dftrpred4g
  let vy: setvar y
  let cA: class A
  let cR: class R
  let cX: class X

  disjoint A y
  disjoint R y
  disjoint X y
  assert |- ( ( X e. A /\ R Se A ) -> TrPred ( R , A , X ) = U_ y e. Pred ( R , A , X ) ( { y } u. TrPred ( R , A , y ) ) )

  proof
    cX
    cA
    wcel
    cA
    cR
    wse
    wa
    cA
    cR
    cX
    ctrpred
    cA
    cR
    cX
    cpred
    #
    vy
    @0
    cA
    cR
    vy
    cv
    #
    ctrpred
    #
    ciun
    #
    cun
    #
    vy
    @0
    @1
    csn
    #
    @2
    cun
    ciun
    #
    vy
    cA
    cR
    cX
    dftrpred3g
    @6
    vy
    @0
    @5
    ciun
    #
    @3
    cun
    @4
    vy
    @0
    @5
    @2
    iunun
    @7
    @0
    @3
    vy
    @0
    iunid
    uneq1i
    eqtri
    syl6eqr
end
