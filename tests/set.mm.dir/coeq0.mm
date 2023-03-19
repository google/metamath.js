include "ccom.mm"
include "c0.mm"
include "wceq.mm"
include "crn.mm"
include "cres.mm"
include "cdm.mm"
include "cin.mm"
include "wrel.mm"
include "wb.mm"
include "relco.mm"
include "relrn0.mm"
include "ax-mp.mm"
include "rnco.mm"
include "eqeq1i.mm"
include "relres.mm"
include "reldm0.mm"
include "dmres.mm"
include "incom.mm"
include "eqtri.mm"
include "3bitr3i.mm"
include "3bitri.mm"

theorem coeq0
  let cA: class A
  let cB: class B


  assert |- ( ( A o. B ) = (/) <-> ( dom A i^i ran B ) = (/) )

  proof
    cA
    cB
    ccom
    #
    c0
    wceq
    #
    @0
    crn
    #
    c0
    wceq
    #
    cA
    cB
    crn
    #
    cres
    #
    crn
    #
    c0
    wceq
    #
    cA
    cdm
    #
    @4
    cin
    #
    c0
    wceq
    #
    @0
    wrel
    @1
    @3
    wb
    cA
    cB
    relco
    @0
    relrn0
    ax-mp
    @2
    @6
    c0
    cA
    cB
    rnco
    eqeq1i
    @5
    c0
    wceq
    #
    @5
    cdm
    #
    c0
    wceq
    #
    @7
    @10
    @5
    wrel
    #
    @11
    @13
    wb
    cA
    @4
    relres
    #
    @5
    reldm0
    ax-mp
    @14
    @11
    @7
    wb
    @15
    @5
    relrn0
    ax-mp
    @12
    @9
    c0
    @12
    @4
    @8
    cin
    @9
    cA
    @4
    dmres
    @4
    @8
    incom
    eqtri
    eqeq1i
    3bitr3i
    3bitri
end
