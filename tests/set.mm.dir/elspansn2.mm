include "chil.mm"
include "wcel.mm"
include "c0v.mm"
include "wne.mm"
include "w3a.mm"
include "csn.mm"
include "cspn.mm"
include "cfv.mm"
include "cort.mm"
include "csp.mm"
include "co.mm"
include "cdiv.mm"
include "csm.mm"
include "wceq.mm"
include "wb.mm"
include "spansn.mm"
include "eleq2d.mm"
include "3ad2ant2.mm"
include "wi.mm"
include "cif.mm"
include "eleq1.mm"
include "id.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "bibi12d.mm"
include "imbi2d.mm"
include "neeq1.mm"
include "sneq.mm"
include "fveq2d.mm"
include "oveq2.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "eqeq2d.mm"
include "imbi12d.mm"
include "ifhvhv0.mm"
include "h1de2bi.mm"
include "dedth2h.mm"
include "3impia.mm"
include "bitrd.mm"

theorem elspansn2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ~H /\ B e. ~H /\ B =/= 0h ) -> ( A e. ( span ` { B } ) <-> A = ( ( ( A .ih B ) / ( B .ih B ) ) .h B ) ) )

  proof
    cA
    chil
    wcel
    #
    cB
    chil
    wcel
    #
    cB
    c0v
    wne
    #
    w3a
    cA
    cB
    csn
    #
    cspn
    cfv
    #
    wcel
    #
    cA
    @3
    cort
    cfv
    #
    cort
    cfv
    #
    wcel
    #
    cA
    cA
    cB
    csp
    co
    #
    cB
    cB
    csp
    co
    #
    cdiv
    co
    #
    cB
    csm
    co
    #
    wceq
    #
    @1
    @0
    @5
    @8
    wb
    @2
    @1
    @4
    @7
    cA
    cB
    spansn
    eleq2d
    3ad2ant2
    @0
    @1
    @2
    @8
    @13
    wb
    #
    @0
    @1
    @2
    @14
    wi
    @2
    @0
    cA
    c0v
    cif
    #
    @7
    wcel
    #
    @15
    @15
    cB
    csp
    co
    #
    @10
    cdiv
    co
    #
    cB
    csm
    co
    #
    wceq
    #
    wb
    #
    wi
    @1
    cB
    c0v
    cif
    #
    c0v
    wne
    #
    @15
    @22
    csn
    #
    cort
    cfv
    #
    cort
    cfv
    #
    wcel
    #
    @15
    @15
    @22
    csp
    co
    #
    @22
    @22
    csp
    co
    #
    cdiv
    co
    #
    @22
    csm
    co
    #
    wceq
    #
    wb
    #
    wi
    cA
    cB
    c0v
    c0v
    cA
    @15
    wceq
    #
    @14
    @21
    @2
    @34
    @8
    @16
    @13
    @20
    cA
    @15
    @7
    eleq1
    @34
    cA
    @15
    @12
    @19
    @34
    id
    @34
    @11
    @18
    cB
    csm
    @34
    @9
    @17
    @10
    cdiv
    cA
    @15
    cB
    csp
    oveq1
    oveq1d
    oveq1d
    eqeq12d
    bibi12d
    imbi2d
    cB
    @22
    wceq
    #
    @2
    @23
    @21
    @33
    cB
    @22
    c0v
    neeq1
    @35
    @16
    @27
    @20
    @32
    @35
    @7
    @26
    @15
    @35
    @6
    @25
    cort
    @35
    @3
    @24
    cort
    cB
    @22
    sneq
    fveq2d
    fveq2d
    eleq2d
    @35
    @19
    @31
    @15
    @35
    @18
    @30
    cB
    @22
    csm
    @35
    @17
    @28
    @10
    @29
    cdiv
    cB
    @22
    @15
    csp
    oveq2
    @35
    @10
    @22
    cB
    csp
    co
    @29
    cB
    @22
    cB
    csp
    oveq1
    cB
    @22
    @22
    csp
    oveq2
    eqtrd
    oveq12d
    @35
    id
    oveq12d
    eqeq2d
    bibi12d
    imbi12d
    @15
    @22
    cA
    ifhvhv0
    cB
    ifhvhv0
    h1de2bi
    dedth2h
    3impia
    bitrd
end
