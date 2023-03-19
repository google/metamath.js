include "cen.mm"
include "wbr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "w3a.mm"
include "ccda.mm"
include "co.mm"
include "cun.mm"
include "cdaen.mm"
include "3adant3.mm"
include "cvv.mm"
include "wcel.mm"
include "relen.mm"
include "brrelex2i.mm"
include "id.mm"
include "cdaun.mm"
include "syl3an.mm"
include "entr.mm"
include "syl2anc.mm"

theorem cdaenun
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A ~~ B /\ C ~~ D /\ ( B i^i D ) = (/) ) -> ( A +c C ) ~~ ( B u. D ) )

  proof
    cA
    cB
    cen
    wbr
    #
    cC
    cD
    cen
    wbr
    #
    cB
    cD
    cin
    c0
    wceq
    #
    w3a
    cA
    cC
    ccda
    co
    #
    cB
    cD
    ccda
    co
    #
    cen
    wbr
    #
    @4
    cB
    cD
    cun
    #
    cen
    wbr
    #
    @3
    @6
    cen
    wbr
    @0
    @1
    @5
    @2
    cA
    cB
    cC
    cD
    cdaen
    3adant3
    @0
    cB
    cvv
    wcel
    @1
    cD
    cvv
    wcel
    @2
    @2
    @7
    cA
    cB
    cen
    relen
    brrelex2i
    cC
    cD
    cen
    relen
    brrelex2i
    @2
    id
    cB
    cD
    cvv
    cvv
    cdaun
    syl3an
    @3
    @4
    @6
    entr
    syl2anc
end
