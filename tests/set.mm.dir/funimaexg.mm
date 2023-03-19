include "wcel.mm"
include "wfun.mm"
include "cima.mm"
include "cvv.mm"
include "cv.mm"
include "wi.mm"
include "wceq.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "imbi2d.mm"
include "cop.mm"
include "wal.mm"
include "wex.mm"
include "wrel.mm"
include "dffun5.mm"
include "simprbi.mm"
include "wel.mm"
include "wa.mm"
include "wb.mm"
include "nfv.mm"
include "axrep4.mm"
include "isset.mm"
include "cab.mm"
include "dfima3.mm"
include "eqeq2i.mm"
include "abeq2.mm"
include "bitri.mm"
include "exbii.mm"
include "sylibr.mm"
include "syl.mm"
include "vtoclg.mm"
include "impcom.mm"

theorem funimaexg
  let cA: class A
  let cB: class B
  let cC: class C
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( ( Fun A /\ B e. C ) -> ( A " B ) e. _V )

  proof
    cB
    cC
    wcel
    cA
    wfun
    #
    cA
    cB
    cima
    #
    cvv
    wcel
    #
    @0
    cA
    vw
    cv
    #
    cima
    #
    cvv
    wcel
    #
    wi
    @0
    @2
    wi
    vw
    cB
    cC
    @3
    cB
    wceq
    #
    @5
    @2
    @0
    @6
    @4
    @1
    cvv
    @3
    cB
    cA
    imaeq2
    eleq1d
    imbi2d
    @0
    vx
    cv
    vy
    cv
    #
    cop
    cA
    wcel
    #
    @7
    vz
    cv
    #
    wceq
    wi
    vy
    wal
    vz
    wex
    vx
    wal
    #
    @5
    @0
    cA
    wrel
    @10
    vx
    vy
    vz
    cA
    dffun5
    simprbi
    @10
    vy
    vz
    wel
    vx
    vw
    wel
    @8
    wa
    vx
    wex
    #
    wb
    vy
    wal
    #
    vz
    wex
    #
    @5
    @8
    vx
    vy
    vz
    vw
    @8
    vz
    nfv
    axrep4
    @5
    @9
    @4
    wceq
    #
    vz
    wex
    @13
    vz
    @4
    isset
    @14
    @12
    vz
    @14
    @9
    @11
    vy
    cab
    #
    wceq
    @12
    @4
    @15
    @9
    vx
    vy
    cA
    @3
    dfima3
    eqeq2i
    @11
    vy
    @9
    abeq2
    bitri
    exbii
    bitri
    sylibr
    syl
    vtoclg
    impcom
end
