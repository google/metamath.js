include "cr.mm"
include "cq.mm"
include "cdif.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "wn.mm"
include "wa.mm"
include "eldif.mm"
include "qre.mm"
include "remulcl.mm"
include "sylan2.mm"
include "ad2ant2r.mm"
include "wi.mm"
include "cdiv.mm"
include "qdivcl.mm"
include "3expb.mm"
include "expcom.mm"
include "adantl.mm"
include "wceq.mm"
include "cc.mm"
include "qcn.mm"
include "recn.mm"
include "divcan4.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "con3d.mm"
include "ex.mm"
include "com23.mm"
include "imp31.mm"
include "jca.mm"
include "3impb.mm"
include "syl3an1b.mm"
include "sylibr.mm"

theorem irrmul
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ( RR \ QQ ) /\ B e. QQ /\ B =/= 0 ) -> ( A x. B ) e. ( RR \ QQ ) )

  proof
    cA
    cr
    cq
    cdif
    #
    wcel
    #
    cB
    cq
    wcel
    #
    cB
    cc0
    wne
    #
    w3a
    cA
    cB
    cmul
    co
    #
    cr
    wcel
    #
    @4
    cq
    wcel
    #
    wn
    #
    wa
    #
    @4
    @0
    wcel
    @1
    cA
    cr
    wcel
    #
    cA
    cq
    wcel
    #
    wn
    #
    wa
    #
    @2
    @3
    @8
    cA
    cr
    cq
    eldif
    @12
    @2
    @3
    @8
    @12
    @2
    @3
    wa
    #
    wa
    @5
    @7
    @9
    @2
    @5
    @11
    @3
    @2
    @9
    cB
    cr
    wcel
    @5
    cB
    qre
    cA
    cB
    remulcl
    sylan2
    ad2ant2r
    @9
    @11
    @13
    @7
    @9
    @13
    @11
    @7
    @9
    @13
    @11
    @7
    wi
    @9
    @13
    wa
    #
    @6
    @10
    @14
    @6
    @4
    cB
    cdiv
    co
    #
    cq
    wcel
    #
    @10
    @13
    @6
    @16
    wi
    @9
    @6
    @13
    @16
    @6
    @2
    @3
    @16
    @4
    cB
    qdivcl
    3expb
    expcom
    adantl
    @14
    @15
    cA
    cq
    @9
    @2
    @3
    @15
    cA
    wceq
    #
    @2
    @9
    cB
    cc
    wcel
    #
    @3
    @17
    cB
    qcn
    @9
    cA
    cc
    wcel
    @18
    @3
    @17
    cA
    recn
    cA
    cB
    divcan4
    syl3an1
    syl3an2
    3expb
    eleq1d
    sylibd
    con3d
    ex
    com23
    imp31
    jca
    3impb
    syl3an1b
    @4
    cr
    cq
    eldif
    sylibr
end
