include "cn0.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "chash.mm"
include "cfv.mm"
include "cmul.mm"
include "cfn.mm"
include "cc.mm"
include "wceq.mm"
include "fzfid.mm"
include "nn0cn.mm"
include "fsumconst.mm"
include "syl2an.mm"
include "hashfz1.mm"
include "adantr.mm"
include "oveq1d.mm"
include "eqtr2d.mm"

theorem nn0mulfsum
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vx: setvar x

  disjoint A k
  disjoint B k
  disjoint k x
  assert |- ( ( A e. NN0 /\ B e. NN0 ) -> ( A x. B ) = sum_ k e. ( 1 ... A ) B )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    wa
    #
    c1
    cA
    cfz
    co
    #
    cB
    vk
    csu
    #
    @3
    chash
    cfv
    #
    cB
    cmul
    co
    #
    cA
    cB
    cmul
    co
    @0
    @3
    cfn
    wcel
    cB
    cc
    wcel
    @4
    @6
    wceq
    @1
    @0
    c1
    cA
    fzfid
    cB
    nn0cn
    @3
    cB
    vk
    fsumconst
    syl2an
    @2
    @5
    cA
    cB
    cmul
    @0
    @5
    cA
    wceq
    @1
    cA
    hashfz1
    adantr
    oveq1d
    eqtr2d
end
