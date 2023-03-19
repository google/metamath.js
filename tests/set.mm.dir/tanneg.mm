include "cc.mm"
include "wcel.mm"
include "ccos.mm"
include "cfv.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "csin.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "ctan.mm"
include "wceq.mm"
include "coscl.mm"
include "sincl.mm"
include "divneg.mm"
include "syl3an1.mm"
include "syl3an2.mm"
include "3anidm12.mm"
include "tanval.mm"
include "negeqd.mm"
include "cosneg.mm"
include "adantr.mm"
include "simpr.mm"
include "eqnetrd.mm"
include "negcl.mm"
include "sylan.mm"
include "syldan.mm"
include "sinneg.mm"
include "oveq12d.mm"
include "eqtrd.mm"
include "3eqtr4rd.mm"

theorem tanneg
  let cA: class A


  assert |- ( ( A e. CC /\ ( cos ` A ) =/= 0 ) -> ( tan ` -u A ) = -u ( tan ` A ) )

  proof
    cA
    cc
    wcel
    #
    cA
    ccos
    cfv
    #
    cc0
    wne
    #
    wa
    #
    cA
    csin
    cfv
    #
    @1
    cdiv
    co
    #
    cneg
    #
    @4
    cneg
    #
    @1
    cdiv
    co
    #
    cA
    ctan
    cfv
    #
    cneg
    cA
    cneg
    #
    ctan
    cfv
    #
    @0
    @2
    @6
    @8
    wceq
    #
    @0
    @0
    @1
    cc
    wcel
    #
    @2
    @12
    cA
    coscl
    @0
    @4
    cc
    wcel
    @13
    @2
    @12
    cA
    sincl
    @4
    @1
    divneg
    syl3an1
    syl3an2
    3anidm12
    @3
    @9
    @5
    cA
    tanval
    negeqd
    @3
    @11
    @10
    csin
    cfv
    #
    @10
    ccos
    cfv
    #
    cdiv
    co
    #
    @8
    @0
    @2
    @15
    cc0
    wne
    #
    @11
    @16
    wceq
    #
    @3
    @15
    @1
    cc0
    @0
    @15
    @1
    wceq
    @2
    cA
    cosneg
    #
    adantr
    @0
    @2
    simpr
    eqnetrd
    @0
    @10
    cc
    wcel
    @17
    @18
    cA
    negcl
    @10
    tanval
    sylan
    syldan
    @0
    @16
    @8
    wceq
    @2
    @0
    @14
    @7
    @15
    @1
    cdiv
    cA
    sinneg
    @19
    oveq12d
    adantr
    eqtrd
    3eqtr4rd
end
