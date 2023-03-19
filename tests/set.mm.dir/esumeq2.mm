include "wceq.mm"
include "wral.mm"
include "cxrs.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cress.mm"
include "cmpt.mm"
include "ctsu.mm"
include "cuni.mm"
include "cesum.mm"
include "eqid.mm"
include "mpteq12.mm"
include "mpan.mm"
include "oveq2d.mm"
include "unieqd.mm"
include "df-esum.mm"
include "3eqtr4g.mm"

theorem esumeq2
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k

  disjoint A k
  assert |- ( A. k e. A B = C -> sum* k e. A B = sum* k e. A C )

  proof
    cB
    cC
    wceq
    vk
    cA
    wral
    #
    cxrs
    cc0
    cpnf
    cicc
    co
    cress
    co
    #
    vk
    cA
    cB
    cmpt
    #
    ctsu
    co
    #
    cuni
    @1
    vk
    cA
    cC
    cmpt
    #
    ctsu
    co
    #
    cuni
    cA
    cB
    vk
    cesum
    cA
    cC
    vk
    cesum
    @0
    @3
    @5
    @0
    @2
    @4
    @1
    ctsu
    cA
    cA
    wceq
    @0
    @2
    @4
    wceq
    cA
    eqid
    vk
    cA
    cB
    cA
    cC
    mpteq12
    mpan
    oveq2d
    unieqd
    cA
    cB
    vk
    df-esum
    cA
    cC
    vk
    df-esum
    3eqtr4g
end
