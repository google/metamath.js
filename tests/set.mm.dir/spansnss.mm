include "csh.mm"
include "wcel.mm"
include "wa.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cv.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "wrex.mm"
include "chil.mm"
include "wb.mm"
include "shel.mm"
include "elspansn.mm"
include "syl.mm"
include "wi.mm"
include "w3a.mm"
include "shmulcl.mm"
include "eleq1a.mm"
include "3exp.mm"
include "com23.mm"
include "imp.mm"
include "rexlimdv.mm"
include "sylbid.mm"
include "ssrdv.mm"

theorem spansnss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. SH /\ B e. A ) -> ( span ` { B } ) C_ A )

  proof
    cA
    csh
    wcel
    #
    cB
    cA
    wcel
    #
    wa
    #
    vx
    cB
    csn
    cspn
    cfv
    #
    cA
    @2
    vx
    cv
    #
    @3
    wcel
    #
    @4
    vy
    cv
    #
    cB
    csm
    co
    #
    wceq
    #
    vy
    cc
    wrex
    #
    @4
    cA
    wcel
    #
    @2
    cB
    chil
    wcel
    @5
    @9
    wb
    cB
    cA
    shel
    vy
    cB
    @4
    elspansn
    syl
    @2
    @8
    @10
    vy
    cc
    @0
    @1
    @6
    cc
    wcel
    #
    @8
    @10
    wi
    #
    wi
    @0
    @11
    @1
    @12
    @0
    @11
    @1
    @12
    @0
    @11
    @1
    w3a
    @7
    cA
    wcel
    @12
    @6
    cB
    cA
    shmulcl
    @7
    cA
    @4
    eleq1a
    syl
    3exp
    com23
    imp
    rexlimdv
    sylbid
    ssrdv
end
