include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wn.mm"
include "wceq.mm"
include "wo.mm"
include "ltnle.mm"
include "wb.mm"
include "leloe.mm"
include "ancoms.mm"
include "notbid.mm"
include "ioran.mm"
include "a1i.mm"
include "3bitrd.mm"

theorem ltnltne
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A < B <-> ( -. B < A /\ -. B = A ) ) )

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
    clt
    wbr
    cB
    cA
    cle
    wbr
    #
    wn
    cB
    cA
    clt
    wbr
    #
    cB
    cA
    wceq
    #
    wo
    #
    wn
    #
    @4
    wn
    @5
    wn
    wa
    #
    cA
    cB
    ltnle
    @2
    @3
    @6
    @1
    @0
    @3
    @6
    wb
    cB
    cA
    leloe
    ancoms
    notbid
    @7
    @8
    wb
    @2
    @4
    @5
    ioran
    a1i
    3bitrd
end
