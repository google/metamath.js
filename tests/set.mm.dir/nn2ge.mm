include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wrex.mm"
include "cr.mm"
include "nnre.mm"
include "adantr.mm"
include "adantl.mm"
include "leid.mm"
include "biantrud.mm"
include "biimpa.mm"
include "sylan.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syldan.mm"
include "adantll.mm"
include "anim1i.mm"
include "adantlr.mm"
include "lecasei.mm"

theorem nn2ge
  let vx: setvar x
  let cA: class A
  let cB: class B

  disjoint A x
  disjoint B x
  assert |- ( ( A e. NN /\ B e. NN ) -> E. x e. NN ( A <_ x /\ B <_ x ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    cA
    vx
    cv
    #
    cle
    wbr
    #
    cB
    @2
    cle
    wbr
    #
    wa
    #
    vx
    cn
    wrex
    #
    cA
    cB
    @0
    cA
    cr
    wcel
    #
    @1
    cA
    nnre
    #
    adantr
    @1
    cB
    cr
    wcel
    #
    @0
    cB
    nnre
    #
    adantl
    @1
    cA
    cB
    cle
    wbr
    #
    @6
    @0
    @1
    @11
    @11
    cB
    cB
    cle
    wbr
    #
    wa
    #
    @6
    @1
    @9
    @11
    @13
    @10
    @9
    @11
    @13
    @9
    @12
    @11
    cB
    leid
    biantrud
    biimpa
    sylan
    @5
    @13
    vx
    cB
    cn
    @2
    cB
    wceq
    @3
    @11
    @4
    @12
    @2
    cB
    cA
    cle
    breq2
    @2
    cB
    cB
    cle
    breq2
    anbi12d
    rspcev
    syldan
    adantll
    @0
    cB
    cA
    cle
    wbr
    #
    @6
    @1
    @0
    @14
    cA
    cA
    cle
    wbr
    #
    @14
    wa
    #
    @6
    @0
    @7
    @14
    @16
    @8
    @7
    @15
    @14
    cA
    leid
    anim1i
    sylan
    @5
    @16
    vx
    cA
    cn
    @2
    cA
    wceq
    @3
    @15
    @4
    @14
    @2
    cA
    cA
    cle
    breq2
    @2
    cA
    cB
    cle
    breq2
    anbi12d
    rspcev
    syldan
    adantlr
    lecasei
end
