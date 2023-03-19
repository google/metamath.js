include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cshi.mm"
include "co.mm"
include "wbr.mm"
include "cab.mm"
include "cmin.mm"
include "csn.mm"
include "cima.mm"
include "copab.mm"
include "shftfval.mm"
include "breqd.mm"
include "cvv.mm"
include "wb.mm"
include "vex.mm"
include "wceq.mm"
include "eleq1.mm"
include "oveq1.mm"
include "breq1d.mm"
include "anbi12d.mm"
include "breq2.mm"
include "anbi2d.mm"
include "eqid.mm"
include "brabg.mm"
include "mpan2.mm"
include "sylan9bb.mm"
include "ibar.mm"
include "adantl.mm"
include "bitr4d.mm"
include "abbidv.mm"
include "imasng.mm"
include "ovex.mm"
include "mp1i.mm"
include "3eqtr4d.mm"

theorem shftfib
  let cA: class A
  let cB: class B
  let cF: class F
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume shftfval.1: |- F e. _V


  assert |- ( ( A e. CC /\ B e. CC ) -> ( ( F shift A ) " { B } ) = ( F " { ( B - A ) } ) )

  proof
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    cB
    vz
    cv
    #
    cF
    cA
    cshi
    co
    #
    wbr
    #
    vz
    cab
    #
    cB
    cA
    cmin
    co
    #
    @3
    cF
    wbr
    #
    vz
    cab
    #
    @4
    cB
    csn
    cima
    #
    cF
    @7
    csn
    cima
    #
    @2
    @5
    @8
    vz
    @2
    @5
    @1
    @8
    wa
    #
    @8
    @0
    @5
    cB
    @3
    vx
    cv
    #
    cc
    wcel
    #
    @13
    cA
    cmin
    co
    #
    vy
    cv
    #
    cF
    wbr
    #
    wa
    #
    vx
    vy
    copab
    #
    wbr
    #
    @1
    @12
    @0
    @4
    @19
    cB
    @3
    vx
    vy
    cA
    cF
    shftfval.1
    shftfval
    breqd
    @1
    @3
    cvv
    wcel
    @20
    @12
    wb
    vz
    vex
    @18
    @1
    @7
    @16
    cF
    wbr
    #
    wa
    @12
    vx
    vy
    cB
    @3
    cc
    cvv
    @19
    @13
    cB
    wceq
    #
    @14
    @1
    @17
    @21
    @13
    cB
    cc
    eleq1
    @22
    @15
    @7
    @16
    cF
    @13
    cB
    cA
    cmin
    oveq1
    breq1d
    anbi12d
    @16
    @3
    wceq
    @21
    @8
    @1
    @16
    @3
    @7
    cF
    breq2
    anbi2d
    @19
    eqid
    brabg
    mpan2
    sylan9bb
    @1
    @8
    @12
    wb
    @0
    @1
    @8
    ibar
    adantl
    bitr4d
    abbidv
    @1
    @10
    @6
    wceq
    @0
    vz
    cB
    cc
    @4
    imasng
    adantl
    @7
    cvv
    wcel
    @11
    @9
    wceq
    @2
    cB
    cA
    cmin
    ovex
    vz
    @7
    cvv
    cF
    imasng
    mp1i
    3eqtr4d
end
