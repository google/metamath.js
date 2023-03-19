include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "c0v.mm"
include "wceq.mm"
include "wb.mm"
include "cif.mm"
include "eleq2.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "bibi12d.mm"
include "eleq1.mm"
include "ifchhv.mm"
include "ifhvhv0.mm"
include "pjoc1i.mm"
include "dedth2h.mm"

theorem pjoc1
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( A e. H <-> ( ( projh ` ( _|_ ` H ) ) ` A ) = 0h ) )

  proof
    cH
    cch
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    cH
    wcel
    #
    cA
    cH
    cort
    cfv
    #
    cpjh
    cfv
    #
    cfv
    #
    c0v
    wceq
    #
    wb
    cA
    @0
    cH
    chil
    cif
    #
    wcel
    #
    cA
    @7
    cort
    cfv
    #
    cpjh
    cfv
    #
    cfv
    #
    c0v
    wceq
    #
    wb
    @1
    cA
    c0v
    cif
    #
    @7
    wcel
    #
    @13
    @10
    cfv
    #
    c0v
    wceq
    #
    wb
    cH
    cA
    chil
    c0v
    cH
    @7
    wceq
    #
    @2
    @8
    @6
    @12
    cH
    @7
    cA
    eleq2
    @17
    @5
    @11
    c0v
    @17
    cA
    @4
    @10
    @17
    @3
    @9
    cpjh
    cH
    @7
    cort
    fveq2
    fveq2d
    fveq1d
    eqeq1d
    bibi12d
    cA
    @13
    wceq
    #
    @8
    @14
    @12
    @16
    cA
    @13
    @7
    eleq1
    @18
    @11
    @15
    c0v
    cA
    @13
    @10
    fveq2
    eqeq1d
    bibi12d
    @13
    @7
    cH
    ifchhv
    cA
    ifhvhv0
    pjoc1i
    dedth2h
end
