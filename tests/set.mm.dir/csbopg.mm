include "wcel.mm"
include "cvv.mm"
include "wa.mm"
include "csn.mm"
include "cpr.mm"
include "c0.mm"
include "cif.mm"
include "csb.mm"
include "cop.mm"
include "wsbc.mm"
include "csbif.mm"
include "sbcan.mm"
include "sbcel1g.mm"
include "anbi12d.mm"
include "syl5bb.mm"
include "csbprg.mm"
include "csbsng.mm"
include "preq12d.mm"
include "eqtrd.mm"
include "csbconstg.mm"
include "ifbieq12d.mm"
include "syl5eq.mm"
include "dfopif.mm"
include "csbeq2i.mm"
include "3eqtr4g.mm"

theorem csbopg
  let vx: setvar x
  let cA: class A
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( A e. V -> [_ A / x ]_ <. C , D >. = <. [_ A / x ]_ C , [_ A / x ]_ D >. )

  proof
    cA
    cV
    wcel
    #
    vx
    cA
    cC
    cvv
    wcel
    #
    cD
    cvv
    wcel
    #
    wa
    #
    cC
    csn
    #
    cC
    cD
    cpr
    #
    cpr
    #
    c0
    cif
    #
    csb
    #
    vx
    cA
    cC
    csb
    #
    cvv
    wcel
    #
    vx
    cA
    cD
    csb
    #
    cvv
    wcel
    #
    wa
    #
    @9
    csn
    #
    @9
    @11
    cpr
    #
    cpr
    #
    c0
    cif
    #
    vx
    cA
    cC
    cD
    cop
    #
    csb
    @9
    @11
    cop
    @0
    @8
    @3
    vx
    cA
    wsbc
    #
    vx
    cA
    @6
    csb
    #
    vx
    cA
    c0
    csb
    #
    cif
    @17
    @3
    vx
    cA
    @6
    c0
    csbif
    @0
    @19
    @13
    @20
    @21
    @16
    c0
    @19
    @1
    vx
    cA
    wsbc
    #
    @2
    vx
    cA
    wsbc
    #
    wa
    @0
    @13
    @1
    @2
    vx
    cA
    sbcan
    @0
    @22
    @10
    @23
    @12
    vx
    cA
    cC
    cvv
    cV
    sbcel1g
    vx
    cA
    cD
    cvv
    cV
    sbcel1g
    anbi12d
    syl5bb
    @0
    @20
    vx
    cA
    @4
    csb
    #
    vx
    cA
    @5
    csb
    #
    cpr
    @16
    vx
    @4
    @5
    cA
    cV
    csbprg
    @0
    @24
    @14
    @25
    @15
    vx
    cA
    cC
    cV
    csbsng
    vx
    cC
    cD
    cA
    cV
    csbprg
    preq12d
    eqtrd
    vx
    cA
    c0
    cV
    csbconstg
    ifbieq12d
    syl5eq
    vx
    cA
    @18
    @7
    cC
    cD
    dfopif
    csbeq2i
    @9
    @11
    dfopif
    3eqtr4g
end
