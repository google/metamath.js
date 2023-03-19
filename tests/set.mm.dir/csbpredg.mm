include "wcel.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cin.mm"
include "csb.mm"
include "cpred.mm"
include "csbin.mm"
include "csbima12.mm"
include "csbcnv.mm"
include "imaeq1i.mm"
include "csbsng.mm"
include "imaeq2d.mm"
include "syl5eqr.mm"
include "syl5eq.mm"
include "ineq2d.mm"
include "df-pred.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbpredg
  let vx: setvar x
  let cA: class A
  let cD: class D
  let cR: class R
  let cV: class V
  let cX: class X


  assert |- ( A e. V -> [_ A / x ]_ Pred ( R , D , X ) = Pred ( [_ A / x ]_ R , [_ A / x ]_ D , [_ A / x ]_ X ) )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cD
    cR
    ccnv
    #
    cX
    csn
    #
    cima
    #
    cin
    #
    csb
    #
    vx
    cA
    cD
    csb
    #
    vx
    cA
    cR
    csb
    #
    ccnv
    #
    vx
    cA
    cX
    csb
    #
    csn
    #
    cima
    #
    cin
    #
    vx
    cA
    cD
    cR
    cX
    cpred
    #
    csb
    @6
    @7
    @9
    cpred
    @0
    @5
    @6
    vx
    cA
    @3
    csb
    #
    cin
    @12
    vx
    cA
    cD
    @3
    csbin
    @0
    @14
    @11
    @6
    @0
    @14
    vx
    cA
    @1
    csb
    #
    vx
    cA
    @2
    csb
    #
    cima
    #
    @11
    vx
    cA
    @2
    @1
    csbima12
    @0
    @17
    @8
    @16
    cima
    @11
    @8
    @15
    @16
    vx
    cA
    cR
    csbcnv
    imaeq1i
    @0
    @16
    @10
    @8
    vx
    cA
    cX
    cV
    csbsng
    imaeq2d
    syl5eqr
    syl5eq
    ineq2d
    syl5eq
    vx
    cA
    @13
    @4
    cD
    cR
    cX
    df-pred
    csbeq2i
    @6
    @7
    @9
    df-pred
    3eqtr4g
end
