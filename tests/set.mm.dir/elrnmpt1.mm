include "wcel.mm"
include "cv.mm"
include "crn.mm"
include "csb.mm"
include "wceq.mm"
include "wa.mm"
include "wex.mm"
include "vex.mm"
include "wb.mm"
include "id.mm"
include "csbeq1a.mm"
include "eleq12d.mm"
include "biantrud.mm"
include "bitr2d.mm"
include "equcoms.mm"
include "spcev.mm"
include "wrex.mm"
include "df-rex.mm"
include "nfv.mm"
include "nfcsb1v.mm"
include "nfcri.mm"
include "nfeq2.mm"
include "nfan.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "cbvex.mm"
include "bitri.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "exbidv.mm"
include "syl5bb.mm"
include "rnmpt.mm"
include "elab2g.mm"
include "syl5ibr.mm"
include "impcom.mm"

theorem elrnmpt1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cV: class V
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  assume rnmpt.1: |- F = ( x e. A |-> B )


  assert |- ( ( x e. A /\ B e. V ) -> B e. ran F )

  proof
    cB
    cV
    wcel
    #
    vx
    cv
    #
    cA
    wcel
    #
    cB
    cF
    crn
    #
    wcel
    #
    @2
    @4
    @0
    vz
    cv
    #
    vx
    @5
    cA
    csb
    #
    wcel
    #
    cB
    vx
    @5
    cB
    csb
    #
    wceq
    #
    wa
    #
    vz
    wex
    #
    @10
    @2
    vz
    @1
    vx
    vex
    @10
    @2
    wb
    vx
    vz
    @1
    @5
    wceq
    #
    @2
    @7
    @10
    @12
    @1
    @5
    cA
    @6
    @12
    id
    vx
    @5
    cA
    csbeq1a
    eleq12d
    #
    @12
    @9
    @7
    vx
    @5
    cB
    csbeq1a
    #
    biantrud
    bitr2d
    equcoms
    spcev
    vy
    cv
    #
    cB
    wceq
    #
    vx
    cA
    wrex
    #
    @11
    vy
    cB
    @3
    cV
    @17
    @7
    @15
    @8
    wceq
    #
    wa
    #
    vz
    wex
    #
    @16
    @11
    @17
    @2
    @16
    wa
    #
    vx
    wex
    @20
    @16
    vx
    cA
    df-rex
    @21
    @19
    vx
    vz
    @21
    vz
    nfv
    @7
    @18
    vx
    vx
    vz
    @6
    vx
    @5
    cA
    nfcsb1v
    nfcri
    vx
    @15
    @8
    vx
    @5
    cB
    nfcsb1v
    nfeq2
    nfan
    @12
    @2
    @7
    @16
    @18
    @13
    @12
    cB
    @8
    @15
    @14
    eqeq2d
    anbi12d
    cbvex
    bitri
    @16
    @19
    @10
    vz
    @16
    @18
    @9
    @7
    @15
    cB
    @8
    eqeq1
    anbi2d
    exbidv
    syl5bb
    vx
    vy
    cA
    cB
    cF
    rnmpt.1
    rnmpt
    elab2g
    syl5ibr
    impcom
end
