include "co.mm"
include "csb.mm"
include "csbov123.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "csbconstg.mm"
include "oveq12d.mm"
include "wn.mm"
include "c0.mm"
include "cop.mm"
include "cfv.mm"
include "0fv.mm"
include "df-ov.mm"
include "eqtri.mm"
include "3eqtr4ri.mm"
include "csbprc.mm"
include "oveqd.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem csbov
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F

  disjoint B x
  disjoint C x
  assert |- [_ A / x ]_ ( B F C ) = ( B [_ A / x ]_ F C )

  proof
    vx
    cA
    cB
    cC
    cF
    co
    csb
    vx
    cA
    cB
    csb
    #
    vx
    cA
    cC
    csb
    #
    vx
    cA
    cF
    csb
    #
    co
    #
    cB
    cC
    @2
    co
    #
    vx
    cA
    cB
    cC
    cF
    csbov123
    cA
    cvv
    wcel
    #
    @3
    @4
    wceq
    @5
    @0
    cB
    @1
    cC
    @2
    vx
    cA
    cB
    cvv
    csbconstg
    vx
    cA
    cC
    cvv
    csbconstg
    oveq12d
    @5
    wn
    #
    @0
    @1
    c0
    co
    #
    cB
    cC
    c0
    co
    #
    @3
    @4
    cB
    cC
    cop
    #
    c0
    cfv
    c0
    @8
    @7
    @9
    0fv
    cB
    cC
    c0
    df-ov
    @7
    @0
    @1
    cop
    #
    c0
    cfv
    c0
    @0
    @1
    c0
    df-ov
    @10
    0fv
    eqtri
    3eqtr4ri
    @6
    @2
    c0
    @0
    @1
    vx
    cA
    cF
    csbprc
    #
    oveqd
    @6
    @2
    c0
    cB
    cC
    @11
    oveqd
    3eqtr4a
    pm2.61i
    eqtri
end
