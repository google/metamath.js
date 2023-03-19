include "cch.mm"
include "wcel.mm"
include "cat.mm"
include "wa.mm"
include "wss.mm"
include "wn.mm"
include "chj.mm"
include "co.mm"
include "wpss.mm"
include "ccv.mm"
include "wbr.mm"
include "wb.mm"
include "atelch.mm"
include "chnle.mm"
include "sylan2.mm"
include "chcv1.mm"
include "bitr3d.mm"

theorem chcv2
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. CH /\ B e. HAtoms ) -> ( A C. ( A vH B ) <-> A <oH ( A vH B ) ) )

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
    cB
    cA
    wss
    wn
    #
    cA
    cA
    cB
    chj
    co
    #
    wpss
    #
    cA
    @3
    ccv
    wbr
    @1
    @0
    cB
    cch
    wcel
    @2
    @4
    wb
    cB
    atelch
    cA
    cB
    chnle
    sylan2
    cA
    cB
    chcv1
    bitr3d
end
