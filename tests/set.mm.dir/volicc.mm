include "cr.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cicc.mm"
include "co.mm"
include "cvol.mm"
include "cfv.mm"
include "covol.mm"
include "cmin.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "iccmbl.mm"
include "mblvol.mm"
include "syl.mm"
include "3adant3.mm"
include "ovolicc.mm"
include "eqtrd.mm"

theorem volicc
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( A e. RR /\ B e. RR /\ A <_ B ) -> ( vol ` ( A [,] B ) ) = ( B - A ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    w3a
    cA
    cB
    cicc
    co
    #
    cvol
    cfv
    #
    @3
    covol
    cfv
    #
    cB
    cA
    cmin
    co
    @0
    @1
    @4
    @5
    wceq
    #
    @2
    @0
    @1
    wa
    @3
    cvol
    cdm
    wcel
    @6
    cA
    cB
    iccmbl
    @3
    mblvol
    syl
    3adant3
    cA
    cB
    ovolicc
    eqtrd
end
