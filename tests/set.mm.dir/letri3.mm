include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "cle.mm"
include "lttri3.mm"
include "ancom.mm"
include "syl6bbr.mm"
include "lenlt.mm"
include "wb.mm"
include "ancoms.mm"
include "anbi12d.mm"
include "bitr4d.mm"

theorem letri3
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A = B <-> ( A <_ B /\ B <_ A ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cA
    cB
    wceq
    #
    cB
    cA
    clt
    wbr
    wn
    #
    cA
    cB
    clt
    wbr
    wn
    #
    wa
    #
    cA
    cB
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    #
    wa
    @2
    @3
    @5
    @4
    wa
    @6
    cA
    cB
    lttri3
    @4
    @5
    ancom
    syl6bbr
    @2
    @7
    @4
    @8
    @5
    cA
    cB
    lenlt
    @1
    @0
    @8
    @5
    wb
    cB
    cA
    lenlt
    ancoms
    anbi12d
    bitr4d
end
