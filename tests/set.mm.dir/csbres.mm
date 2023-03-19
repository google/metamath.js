include "cres.mm"
include "csb.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "df-res.mm"
include "csbeq2i.mm"
include "wcel.mm"
include "wceq.mm"
include "csbxp.mm"
include "csbconstg.mm"
include "xpeq2d.mm"
include "syl5eq.mm"
include "wn.mm"
include "c0.mm"
include "0xp.mm"
include "a1i.mm"
include "csbprc.mm"
include "xpeq1d.mm"
include "3eqtr4rd.mm"
include "pm2.61i.mm"
include "ineq2i.mm"
include "csbin.mm"
include "3eqtr4i.mm"
include "eqtri.mm"

theorem csbres
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- [_ A / x ]_ ( B |` C ) = ( [_ A / x ]_ B |` [_ A / x ]_ C )

  proof
    vx
    cA
    cB
    cC
    cres
    #
    csb
    vx
    cA
    cB
    cC
    cvv
    cxp
    #
    cin
    #
    csb
    #
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
    cres
    #
    vx
    cA
    @0
    @2
    cB
    cC
    df-res
    csbeq2i
    @4
    vx
    cA
    @1
    csb
    #
    cin
    @4
    @5
    cvv
    cxp
    #
    cin
    @3
    @6
    @7
    @8
    @4
    cA
    cvv
    wcel
    #
    @7
    @8
    wceq
    @9
    @7
    @5
    vx
    cA
    cvv
    csb
    #
    cxp
    @8
    vx
    cA
    cC
    cvv
    csbxp
    @9
    @10
    cvv
    @5
    vx
    cA
    cvv
    cvv
    csbconstg
    xpeq2d
    syl5eq
    @9
    wn
    #
    c0
    cvv
    cxp
    #
    c0
    @8
    @7
    @12
    c0
    wceq
    @11
    cvv
    0xp
    a1i
    @11
    @5
    c0
    cvv
    vx
    cA
    cC
    csbprc
    xpeq1d
    vx
    cA
    @1
    csbprc
    3eqtr4rd
    pm2.61i
    ineq2i
    vx
    cA
    cB
    @1
    csbin
    @4
    @5
    df-res
    3eqtr4i
    eqtri
end
