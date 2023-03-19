include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cfl.mm"
include "cfv.mm"
include "cle.mm"
include "wn.mm"
include "flge.mm"
include "wb.mm"
include "zre.mm"
include "lenlt.mm"
include "sylan.mm"
include "ancoms.mm"
include "reflcl.mm"
include "syl2anr.mm"
include "3bitr3d.mm"
include "con4bid.mm"

theorem fllt
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. ZZ ) -> ( A < B <-> ( |_ ` A ) < B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cfl
    cfv
    #
    cB
    clt
    wbr
    #
    @2
    cB
    cA
    cle
    wbr
    #
    cB
    @4
    cle
    wbr
    #
    @3
    wn
    #
    @5
    wn
    #
    cA
    cB
    flge
    @1
    @0
    @6
    @8
    wb
    #
    @1
    cB
    cr
    wcel
    #
    @0
    @10
    cB
    zre
    #
    cB
    cA
    lenlt
    sylan
    ancoms
    @1
    @11
    @4
    cr
    wcel
    @7
    @9
    wb
    @0
    @12
    cA
    reflcl
    cB
    @4
    lenlt
    syl2anr
    3bitr3d
    con4bid
end
