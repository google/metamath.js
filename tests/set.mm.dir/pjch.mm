include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cpjh.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "cif.mm"
include "c0v.mm"
include "eleq2.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "bibi12d.mm"
include "eleq1.mm"
include "id.mm"
include "eqeq12d.mm"
include "ifchhv.mm"
include "ifhvhv0.mm"
include "pjchi.mm"
include "dedth2h.mm"

theorem pjch
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( A e. H <-> ( ( projh ` H ) ` A ) = A ) )

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
    cpjh
    cfv
    #
    cfv
    #
    cA
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
    @6
    cpjh
    cfv
    #
    cfv
    #
    cA
    wceq
    #
    wb
    @1
    cA
    c0v
    cif
    #
    @6
    wcel
    #
    @11
    @8
    cfv
    #
    @11
    wceq
    #
    wb
    cH
    cA
    chil
    c0v
    cH
    @6
    wceq
    #
    @2
    @7
    @5
    @10
    cH
    @6
    cA
    eleq2
    @15
    @4
    @9
    cA
    @15
    cA
    @3
    @8
    cH
    @6
    cpjh
    fveq2
    fveq1d
    eqeq1d
    bibi12d
    cA
    @11
    wceq
    #
    @7
    @12
    @10
    @14
    cA
    @11
    @6
    eleq1
    @16
    @9
    @13
    cA
    @11
    cA
    @11
    @8
    fveq2
    @16
    id
    eqeq12d
    bibi12d
    @11
    @6
    cH
    ifchhv
    cA
    ifhvhv0
    pjchi
    dedth2h
end
