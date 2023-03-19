include "cch.mm"
include "wcel.mm"
include "chil.mm"
include "cort.mm"
include "cfv.mm"
include "cpjh.mm"
include "c0v.mm"
include "wceq.mm"
include "wb.mm"
include "c0h.mm"
include "cif.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "fveq1d.mm"
include "eqeq1d.mm"
include "bibi12d.mm"
include "eleq1.mm"
include "h0elch.mm"
include "elimel.mm"
include "ifhvhv0.mm"
include "pjoc2i.mm"
include "dedth2h.mm"

theorem pjoc2
  let cA: class A
  let cH: class H


  assert |- ( ( H e. CH /\ A e. ~H ) -> ( A e. ( _|_ ` H ) <-> ( ( projh ` H ) ` A ) = 0h ) )

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
    cort
    cfv
    #
    wcel
    #
    cA
    cH
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
    c0h
    cif
    #
    cort
    cfv
    #
    wcel
    #
    cA
    @7
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
    @8
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
    c0h
    c0v
    cH
    @7
    wceq
    #
    @3
    @9
    @6
    @12
    @17
    @2
    @8
    cA
    cH
    @7
    cort
    fveq2
    eleq2d
    @17
    @5
    @11
    c0v
    @17
    cA
    @4
    @10
    cH
    @7
    cpjh
    fveq2
    fveq1d
    eqeq1d
    bibi12d
    cA
    @13
    wceq
    #
    @9
    @14
    @12
    @16
    cA
    @13
    @8
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
    c0h
    cch
    h0elch
    elimel
    cA
    ifhvhv0
    pjoc2i
    dedth2h
end
