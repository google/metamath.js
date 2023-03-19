include "wcel.mm"
include "cvv.mm"
include "cplusr.mm"
include "co.mm"
include "cr.mm"
include "cv.mm"
include "cfv.mm"
include "caddc.mm"
include "cmpt.mm"
include "wceq.mm"
include "elex.mm"
include "wa.mm"
include "fveq1.mm"
include "oveqan12d.mm"
include "mpteq2dv.mm"
include "df-addr.mm"
include "reex.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "syl2an.mm"

theorem addrval
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
  assert |- ( ( A e. C /\ B e. D ) -> ( A +r B ) = ( v e. RR |-> ( ( A ` v ) + ( B ` v ) ) ) )

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
    cplusr
    co
    vv
    cr
    vv
    cv
    #
    cA
    cfv
    #
    @0
    cB
    cfv
    #
    caddc
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
    @0
    vx
    cv
    #
    cfv
    #
    @0
    vy
    cv
    #
    cfv
    #
    caddc
    co
    #
    cmpt
    @4
    cplusr
    @5
    cA
    wceq
    #
    @7
    cB
    wceq
    #
    wa
    vv
    cr
    @9
    @3
    @10
    @11
    @6
    @1
    @8
    @2
    caddc
    @0
    @5
    cA
    fveq1
    @0
    @7
    cB
    fveq1
    oveqan12d
    mpteq2dv
    vx
    vy
    vv
    df-addr
    vv
    cr
    @3
    reex
    mptex
    ovmpt2a
    syl2an
end
