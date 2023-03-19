include "cvv.mm"
include "cima.mm"
include "csb.mm"
include "crn.mm"
include "csbima12.mm"
include "wcel.mm"
include "wceq.mm"
include "csbconstg.mm"
include "imaeq2d.mm"
include "wn.mm"
include "c0.mm"
include "0ima.mm"
include "eqcomi.mm"
include "csbprc.mm"
include "imaeq1d.mm"
include "syl6eq.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"
include "dfrn4.mm"
include "csbeq2i.mm"
include "3eqtr4i.mm"

theorem csbrn
  let vx: setvar x
  let cA: class A
  let cB: class B


  assert |- [_ A / x ]_ ran B = ran [_ A / x ]_ B

  proof
    vx
    cA
    cB
    cvv
    cima
    #
    csb
    #
    vx
    cA
    cB
    csb
    #
    cvv
    cima
    #
    vx
    cA
    cB
    crn
    #
    csb
    @2
    crn
    @1
    @2
    vx
    cA
    cvv
    csb
    #
    cima
    #
    @3
    vx
    cA
    cvv
    cB
    csbima12
    cA
    cvv
    wcel
    #
    @6
    @3
    wceq
    @7
    @5
    cvv
    @2
    vx
    cA
    cvv
    cvv
    csbconstg
    imaeq2d
    @7
    wn
    #
    c0
    c0
    cvv
    cima
    #
    @6
    @3
    @9
    c0
    cvv
    0ima
    eqcomi
    @8
    @6
    c0
    @5
    cima
    c0
    @8
    @2
    c0
    @5
    vx
    cA
    cB
    csbprc
    #
    imaeq1d
    @5
    0ima
    syl6eq
    @8
    @2
    c0
    cvv
    @10
    imaeq1d
    3eqtr4a
    pm2.61i
    eqtri
    vx
    cA
    @4
    @0
    cB
    dfrn4
    csbeq2i
    @2
    dfrn4
    3eqtr4i
end
