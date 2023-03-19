include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "clt.mm"
include "msqgt0.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "sqval.mm"
include "syl.mm"
include "adantr.mm"
include "breqtrrd.mm"

theorem sqgt0
  let cA: class A


  assert |- ( ( A e. RR /\ A =/= 0 ) -> 0 < ( A ^ 2 ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    cc0
    cA
    cA
    cmul
    co
    #
    cA
    c2
    cexp
    co
    #
    clt
    cA
    msqgt0
    @0
    @3
    @2
    wceq
    #
    @1
    @0
    cA
    cc
    wcel
    @4
    cA
    recn
    cA
    sqval
    syl
    adantr
    breqtrrd
end
