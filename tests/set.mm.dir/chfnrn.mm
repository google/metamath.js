include "wfn.mm"
include "cv.mm"
include "cfv.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "crn.mm"
include "cuni.mm"
include "wrex.mm"
include "wceq.mm"
include "fvelrnb.mm"
include "biimpd.mm"
include "wi.mm"
include "eleq1.mm"
include "biimpcd.mm"
include "ralimi.mm"
include "rexim.mm"
include "syl.mm"
include "sylan9.mm"
include "eluni2.mm"
include "syl6ibr.mm"
include "ssrdv.mm"

theorem chfnrn
  let vx: setvar x
  let cA: class A
  let cF: class F
  let vy: setvar y

  disjoint A x
  disjoint F x
  disjoint x y
  disjoint A y
  disjoint F y
  assert |- ( ( F Fn A /\ A. x e. A ( F ` x ) e. x ) -> ran F C_ U. A )

  proof
    cF
    cA
    wfn
    #
    vx
    cv
    #
    cF
    cfv
    #
    @1
    wcel
    #
    vx
    cA
    wral
    #
    wa
    #
    vy
    cF
    crn
    #
    cA
    cuni
    #
    @5
    vy
    cv
    #
    @6
    wcel
    #
    @8
    @1
    wcel
    #
    vx
    cA
    wrex
    #
    @8
    @7
    wcel
    @0
    @9
    @2
    @8
    wceq
    #
    vx
    cA
    wrex
    #
    @4
    @11
    @0
    @9
    @13
    vx
    cA
    @8
    cF
    fvelrnb
    biimpd
    @4
    @12
    @10
    wi
    #
    vx
    cA
    wral
    @13
    @11
    wi
    @3
    @14
    vx
    cA
    @12
    @3
    @10
    @2
    @8
    @1
    eleq1
    biimpcd
    ralimi
    @12
    @10
    vx
    cA
    rexim
    syl
    sylan9
    vx
    @8
    cA
    eluni2
    syl6ibr
    ssrdv
end
