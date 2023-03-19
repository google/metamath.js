include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "wa.mm"
include "cdmd.mm"
include "wbr.mm"
include "atdmd.mm"
include "ancoms.mm"
include "wb.mm"
include "atelch.mm"
include "dmdsym.mm"
include "sylan2.mm"
include "mpbird.mm"

theorem atdmd2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CH /\ B e. HAtoms ) -> A MH* B )

  proof
    cA
    cch
    wcel
    #
    cB
    cat
    wcel
    #
    wa
    cA
    cB
    cdmd
    wbr
    #
    cB
    cA
    cdmd
    wbr
    #
    @1
    @0
    @3
    cB
    cA
    atdmd
    ancoms
    @1
    @0
    cB
    cch
    wcel
    @2
    @3
    wb
    cB
    atelch
    cA
    cB
    dmdsym
    sylan2
    mpbird
end
