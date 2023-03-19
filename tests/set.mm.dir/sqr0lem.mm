include "cc.mm"
include "wcel.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "ci.mm"
include "cmul.mm"
include "crp.mm"
include "wnel.mm"
include "w3a.mm"
include "wa.mm"
include "sqeq0.mm"
include "biimpa.mm"
include "3ad2antr1.mm"
include "cr.mm"
include "0re.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "recnd.mm"
include "sq0i.mm"
include "0le0.mm"
include "fveq2.mm"
include "re0.mm"
include "syl6eq.mm"
include "syl5breqr.mm"
include "rennim.mm"
include "syl.mm"
include "3jca.mm"
include "jca.mm"
include "impbii.mm"

theorem sqr0lem
  let cA: class A


  assert |- ( ( A e. CC /\ ( ( A ^ 2 ) = 0 /\ 0 <_ ( Re ` A ) /\ ( _i x. A ) e/ RR+ ) ) <-> A = 0 )

  proof
    cA
    cc
    wcel
    #
    cA
    c2
    cexp
    co
    cc0
    wceq
    #
    cc0
    cA
    cre
    cfv
    #
    cle
    wbr
    #
    ci
    cA
    cmul
    co
    crp
    wnel
    #
    w3a
    #
    wa
    cA
    cc0
    wceq
    #
    @0
    @3
    @1
    @6
    @4
    @0
    @1
    @6
    cA
    sqeq0
    biimpa
    3ad2antr1
    @6
    @0
    @5
    @6
    cA
    @6
    cA
    cr
    wcel
    #
    cc0
    cr
    wcel
    0re
    cA
    cc0
    cr
    eleq1
    mpbiri
    #
    recnd
    @6
    @1
    @3
    @4
    cA
    sq0i
    @6
    cc0
    cc0
    @2
    cle
    0le0
    @6
    @2
    cc0
    cre
    cfv
    cc0
    cA
    cc0
    cre
    fveq2
    re0
    syl6eq
    syl5breqr
    @6
    @7
    @4
    @8
    cA
    rennim
    syl
    3jca
    jca
    impbii
end
