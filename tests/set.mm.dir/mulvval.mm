include "wcel.mm"
include "cvv.mm"
include "ctimesr.mm"
include "co.mm"
include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "wa.mm"
include "fveq1.mm"
include "oveq12.mm"
include "sylan2.mm"
include "mpteq2dv.mm"
include "df-mulv.mm"
include "reex.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "syl2an.mm"

theorem mulvval
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vx: setvar x
  let vy: setvar y

  disjoint A v
  disjoint B v
  disjoint v x
  disjoint v y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  assert |- ( ( A e. C /\ B e. D ) -> ( A .v B ) = ( v e. RR |-> ( A x. ( B ` v ) ) ) )

  proof
    cA
    cC
    wcel
    cA
    cvv
    wcel
    cB
    cvv
    wcel
    cA
    cB
    ctimesr
    co
    vv
    cr
    cA
    vv
    cv
    #
    cB
    cfv
    #
    cmul
    co
    #
    cmpt
    #
    wceq
    cB
    cD
    wcel
    cA
    cC
    elex
    cB
    cD
    elex
    vx
    vy
    cA
    cB
    cvv
    cvv
    vv
    cr
    vx
    cv
    #
    @0
    vy
    cv
    #
    cfv
    #
    cmul
    co
    #
    cmpt
    @3
    ctimesr
    @4
    cA
    wceq
    #
    @5
    cB
    wceq
    #
    wa
    vv
    cr
    @7
    @2
    @9
    @8
    @6
    @1
    wceq
    @7
    @2
    wceq
    @0
    @5
    cB
    fveq1
    @4
    cA
    @6
    @1
    cmul
    oveq12
    sylan2
    mpteq2dv
    vx
    vy
    vv
    df-mulv
    vv
    cr
    @2
    reex
    mptex
    ovmpt2a
    syl2an
end
