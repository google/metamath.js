include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "crp.mm"
include "clogb.mm"
include "co.mm"
include "cr.mm"
include "cc0.mm"
include "wne.mm"
include "c1.mm"
include "w3a.mm"
include "wi.mm"
include "zgt1rpn0n1.mm"
include "relogbcl.mm"
include "3com23.mm"
include "3expia.mm"
include "3adant2.mm"
include "syl.mm"
include "imp.mm"

theorem relogbzcl
  let cB: class B
  let cX: class X


  assert |- ( ( B e. ( ZZ>= ` 2 ) /\ X e. RR+ ) -> ( B logb X ) e. RR )

  proof
    cB
    c2
    cuz
    cfv
    wcel
    #
    cX
    crp
    wcel
    #
    cB
    cX
    clogb
    co
    cr
    wcel
    #
    @0
    cB
    crp
    wcel
    #
    cB
    cc0
    wne
    #
    cB
    c1
    wne
    #
    w3a
    @1
    @2
    wi
    #
    cB
    zgt1rpn0n1
    @3
    @5
    @6
    @4
    @3
    @5
    @1
    @2
    @3
    @1
    @5
    @2
    cB
    cX
    relogbcl
    3com23
    3expia
    3adant2
    syl
    imp
end
