include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cle.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "pm3.2.mm"
include "pm2.43i.mm"
include "adantr.mm"
include "leid.mm"
include "anim2i.mm"
include "ancoms.mm"
include "jca.mm"
include "ad2antlr.mm"
include "3adantl2.mm"
include "id.mm"
include "ad2ant2r.mm"
include "simplr.mm"
include "anim1i.mm"
include "3adantl3.mm"
include "lediv12a.mm"
include "syl2anc.mm"

theorem lediv2a
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) /\ ( C e. RR /\ 0 <_ C ) ) /\ A <_ B ) -> ( C / B ) <_ ( C / A ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    cle
    wbr
    #
    wa
    #
    w3a
    cA
    cB
    cle
    wbr
    #
    wa
    @6
    @6
    wa
    #
    @7
    cC
    cC
    cle
    wbr
    #
    wa
    #
    wa
    #
    @0
    @3
    wa
    #
    @1
    @9
    wa
    #
    wa
    #
    cC
    cB
    cdiv
    co
    cC
    cA
    cdiv
    co
    cle
    wbr
    @2
    @8
    @9
    @13
    @5
    @8
    @13
    @2
    @9
    @8
    @10
    @12
    @6
    @10
    @7
    @6
    @10
    @6
    @6
    pm3.2
    pm2.43i
    adantr
    @7
    @6
    @12
    @6
    @11
    @7
    cC
    leid
    anim2i
    ancoms
    jca
    ad2antlr
    3adantl2
    @2
    @5
    @9
    @16
    @8
    @2
    @5
    wa
    #
    @9
    wa
    @14
    @15
    @17
    @14
    @9
    @0
    @3
    @14
    @1
    @4
    @14
    id
    ad2ant2r
    adantr
    @17
    @1
    @9
    @0
    @1
    @5
    simplr
    anim1i
    jca
    3adantl3
    cC
    cC
    cA
    cB
    lediv12a
    syl2anc
end
