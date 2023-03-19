include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cioo.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "covol.mm"
include "cmin.mm"
include "cdm.mm"
include "wceq.mm"
include "ioombl.mm"
include "mblvol.mm"
include "ax-mp.mm"
include "ovolioo.mm"
include "syl5eq.mm"

theorem volioo
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( vol ` ( A (,) B ) ) = ( B - A ) )

  proof
    cA
    cr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cle
    wbr
    w3a
    cA
    cB
    cioo
    co
    #
    cvol
    cfv
    #
    @0
    covol
    cfv
    #
    cB
    cA
    cmin
    co
    @0
    cvol
    cdm
    wcel
    @1
    @2
    wceq
    cA
    cB
    ioombl
    @0
    mblvol
    ax-mp
    cA
    cB
    ovolioo
    syl5eq
end
