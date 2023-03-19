include "wnfc.mm"
include "cv.mm"
include "csb.mm"
include "wceq.mm"
include "wal.mm"
include "cvv.mm"
include "wcel.mm"
include "vex.mm"
include "csbtt.mm"
include "mpan.mm"
include "eqtr4d.mm"
include "alrimivv.mm"
include "nfv.mm"
include "wsb.mm"
include "wb.mm"
include "wnf.mm"
include "eleq2.mm"
include "wsbc.mm"
include "sbsbc.mm"
include "sbcel2.mm"
include "bitri.mm"
include "3bitr4g.mm"
include "2alimi.mm"
include "sbnf2.mm"
include "sylibr.mm"
include "nfcd.mm"
include "impbii.mm"

theorem sbnfc2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w

  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  assert |- ( F/_ x A <-> A. y A. z [_ y / x ]_ A = [_ z / x ]_ A )

  proof
    vx
    cA
    wnfc
    #
    vx
    vy
    cv
    #
    cA
    csb
    #
    vx
    vz
    cv
    #
    cA
    csb
    #
    wceq
    #
    vz
    wal
    vy
    wal
    #
    @0
    @5
    vy
    vz
    @0
    @2
    cA
    @4
    @1
    cvv
    wcel
    @0
    @2
    cA
    wceq
    vy
    vex
    vx
    @1
    cA
    cvv
    csbtt
    mpan
    @3
    cvv
    wcel
    @0
    @4
    cA
    wceq
    vz
    vex
    vx
    @3
    cA
    cvv
    csbtt
    mpan
    eqtr4d
    alrimivv
    @6
    vx
    vw
    cA
    @6
    vw
    nfv
    @6
    vw
    cv
    #
    cA
    wcel
    #
    vx
    vy
    wsb
    #
    @8
    vx
    vz
    wsb
    #
    wb
    #
    vz
    wal
    vy
    wal
    @8
    vx
    wnf
    @5
    @11
    vy
    vz
    @5
    @7
    @2
    wcel
    #
    @7
    @4
    wcel
    #
    @9
    @10
    @2
    @4
    @7
    eleq2
    @9
    @8
    vx
    @1
    wsbc
    @12
    @8
    vx
    vy
    sbsbc
    vx
    @1
    @7
    cA
    sbcel2
    bitri
    @10
    @8
    vx
    @3
    wsbc
    @13
    @8
    vx
    vz
    sbsbc
    vx
    @3
    @7
    cA
    sbcel2
    bitri
    3bitr4g
    2alimi
    @8
    vx
    vy
    vz
    sbnf2
    sylibr
    nfcd
    impbii
end
