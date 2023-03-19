include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cneg.mm"
include "cmul.mm"
include "co.mm"
include "renegcl.mm"
include "adantr.mm"
include "lt0neg1.mm"
include "biimpa.mm"
include "jca.mm"
include "mulgt0.mm"
include "syl2an.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "mul2neg.mm"
include "ad2ant2r.mm"
include "breqtrd.mm"

theorem mullt0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ A < 0 ) /\ ( B e. RR /\ B < 0 ) ) -> 0 < ( A x. B ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cB
    cc0
    clt
    wbr
    #
    wa
    #
    wa
    cc0
    cA
    cneg
    #
    cB
    cneg
    #
    cmul
    co
    #
    cA
    cB
    cmul
    co
    #
    clt
    @2
    @6
    cr
    wcel
    #
    cc0
    @6
    clt
    wbr
    #
    wa
    @7
    cr
    wcel
    #
    cc0
    @7
    clt
    wbr
    #
    wa
    cc0
    @8
    clt
    wbr
    @5
    @2
    @10
    @11
    @0
    @10
    @1
    cA
    renegcl
    adantr
    @0
    @1
    @11
    cA
    lt0neg1
    biimpa
    jca
    @5
    @12
    @13
    @3
    @12
    @4
    cB
    renegcl
    adantr
    @3
    @4
    @13
    cB
    lt0neg1
    biimpa
    jca
    @6
    @7
    mulgt0
    syl2an
    @0
    @3
    @8
    @9
    wceq
    #
    @1
    @4
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @14
    @3
    cA
    recn
    cB
    recn
    cA
    cB
    mul2neg
    syl2an
    ad2ant2r
    breqtrd
end
