include "cch.mm"
include "wcel.mm"
include "ccm.mm"
include "wbr.mm"
include "cort.mm"
include "cfv.mm"
include "chj.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wb.mm"
include "c0h.mm"
include "cif.mm"
include "breq1.mm"
include "id.mm"
include "fveq2.mm"
include "oveq1d.mm"
include "ineq12d.mm"
include "ineq1.mm"
include "eqeq12d.mm"
include "bibi12d.mm"
include "breq2.mm"
include "oveq2.mm"
include "ineq2d.mm"
include "ineq2.mm"
include "h0elch.mm"
include "elimel.mm"
include "cmbr3i.mm"
include "dedth2h.mm"

theorem cmbr3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A C_H B <-> ( A i^i ( ( _|_ ` A ) vH B ) ) = ( A i^i B ) ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    cA
    cB
    ccm
    wbr
    #
    cA
    cA
    cort
    cfv
    #
    cB
    chj
    co
    #
    cin
    #
    cA
    cB
    cin
    #
    wceq
    #
    wb
    @0
    cA
    c0h
    cif
    #
    cB
    ccm
    wbr
    #
    @8
    @8
    cort
    cfv
    #
    cB
    chj
    co
    #
    cin
    #
    @8
    cB
    cin
    #
    wceq
    #
    wb
    @8
    @1
    cB
    c0h
    cif
    #
    ccm
    wbr
    #
    @8
    @10
    @15
    chj
    co
    #
    cin
    #
    @8
    @15
    cin
    #
    wceq
    #
    wb
    cA
    cB
    c0h
    c0h
    cA
    @8
    wceq
    #
    @2
    @9
    @7
    @14
    cA
    @8
    cB
    ccm
    breq1
    @21
    @5
    @12
    @6
    @13
    @21
    cA
    @8
    @4
    @11
    @21
    id
    @21
    @3
    @10
    cB
    chj
    cA
    @8
    cort
    fveq2
    oveq1d
    ineq12d
    cA
    @8
    cB
    ineq1
    eqeq12d
    bibi12d
    cB
    @15
    wceq
    #
    @9
    @16
    @14
    @20
    cB
    @15
    @8
    ccm
    breq2
    @22
    @12
    @18
    @13
    @19
    @22
    @11
    @17
    @8
    cB
    @15
    @10
    chj
    oveq2
    ineq2d
    cB
    @15
    @8
    ineq2
    eqeq12d
    bibi12d
    @8
    @15
    cA
    c0h
    cch
    h0elch
    elimel
    cB
    c0h
    cch
    h0elch
    elimel
    cmbr3i
    dedth2h
end
