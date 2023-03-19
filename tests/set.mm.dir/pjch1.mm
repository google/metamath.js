include "chil.mm"
include "wcel.mm"
include "cpjh.mm"
include "cfv.mm"
include "wceq.mm"
include "wb.mm"
include "c0v.mm"
include "cif.mm"
include "eleq1.mm"
include "fveq2.mm"
include "id.mm"
include "eqeq12d.mm"
include "bibi12d.mm"
include "helch.mm"
include "ifhvhv0.mm"
include "pjchi.mm"
include "dedth.mm"
include "ibi.mm"

theorem pjch1
  let cA: class A


  assert |- ( A e. ~H -> ( ( projh ` ~H ) ` A ) = A )

  proof
    cA
    chil
    wcel
    #
    cA
    chil
    cpjh
    cfv
    #
    cfv
    #
    cA
    wceq
    #
    @0
    @0
    @3
    wb
    @0
    cA
    c0v
    cif
    #
    chil
    wcel
    #
    @4
    @1
    cfv
    #
    @4
    wceq
    #
    wb
    cA
    c0v
    cA
    @4
    wceq
    #
    @0
    @5
    @3
    @7
    cA
    @4
    chil
    eleq1
    @8
    @2
    @6
    cA
    @4
    cA
    @4
    @1
    fveq2
    @8
    id
    eqeq12d
    bibi12d
    @4
    chil
    helch
    cA
    ifhvhv0
    pjchi
    dedth
    ibi
end
