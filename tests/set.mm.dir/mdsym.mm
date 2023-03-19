include "cch.mm"
include "wcel.mm"
include "cmd.mm"
include "wbr.mm"
include "wb.mm"
include "chil.mm"
include "cif.mm"
include "wceq.mm"
include "breq1.mm"
include "breq2.mm"
include "bibi12d.mm"
include "ifchhv.mm"
include "mdsymi.mm"
include "dedth2h.mm"

theorem mdsym
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH B <-> B MH A ) )

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
    cmd
    wbr
    #
    cB
    cA
    cmd
    wbr
    #
    wb
    @0
    cA
    chil
    cif
    #
    cB
    cmd
    wbr
    #
    cB
    @4
    cmd
    wbr
    #
    wb
    @4
    @1
    cB
    chil
    cif
    #
    cmd
    wbr
    #
    @7
    @4
    cmd
    wbr
    #
    wb
    cA
    cB
    chil
    chil
    cA
    @4
    wceq
    @2
    @5
    @3
    @6
    cA
    @4
    cB
    cmd
    breq1
    cA
    @4
    cB
    cmd
    breq2
    bibi12d
    cB
    @7
    wceq
    @5
    @8
    @6
    @9
    cB
    @7
    @4
    cmd
    breq2
    cB
    @7
    @4
    cmd
    breq1
    bibi12d
    @4
    @7
    cA
    ifchhv
    cB
    ifchhv
    mdsymi
    dedth2h
end
