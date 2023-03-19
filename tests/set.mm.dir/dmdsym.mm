include "cch.mm"
include "wcel.mm"
include "wa.mm"
include "cort.mm"
include "cfv.mm"
include "cmd.mm"
include "wbr.mm"
include "cdmd.mm"
include "wb.mm"
include "choccl.mm"
include "mdsym.mm"
include "syl2an.mm"
include "dmdmd.mm"
include "ancoms.mm"
include "3bitr4d.mm"

theorem dmdsym
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. CH ) -> ( A MH* B <-> B MH* A ) )

  proof
    cA
    cch
    wcel
    #
    cB
    cch
    wcel
    #
    wa
    cA
    cort
    cfv
    #
    cB
    cort
    cfv
    #
    cmd
    wbr
    #
    @3
    @2
    cmd
    wbr
    #
    cA
    cB
    cdmd
    wbr
    cB
    cA
    cdmd
    wbr
    #
    @0
    @2
    cch
    wcel
    @3
    cch
    wcel
    @4
    @5
    wb
    @1
    cA
    choccl
    cB
    choccl
    @2
    @3
    mdsym
    syl2an
    cA
    cB
    dmdmd
    @1
    @0
    @6
    @5
    wb
    cB
    cA
    dmdmd
    ancoms
    3bitr4d
end
