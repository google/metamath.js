include "cfn.mm"
include "wcel.mm"
include "cc.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "csu.mm"
include "chash.mm"
include "cfv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "wa.mm"
include "wceq.mm"
include "diffi.mm"
include "anim1i.mm"
include "3adant2.mm"
include "fsumconst.mm"
include "syl.mm"
include "hashdifsn.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem fsumdifsnconst
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k

  disjoint A k
  disjoint B k
  disjoint C k
  assert |- ( ( A e. Fin /\ B e. A /\ C e. CC ) -> sum_ k e. ( A \ { B } ) C = ( ( ( # ` A ) - 1 ) x. C ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cA
    wcel
    #
    cC
    cc
    wcel
    #
    w3a
    #
    cA
    cB
    csn
    #
    cdif
    #
    cC
    vk
    csu
    #
    @5
    chash
    cfv
    #
    cC
    cmul
    co
    #
    cA
    chash
    cfv
    c1
    cmin
    co
    #
    cC
    cmul
    co
    @3
    @5
    cfn
    wcel
    #
    @2
    wa
    #
    @6
    @8
    wceq
    @0
    @2
    @11
    @1
    @0
    @10
    @2
    cA
    @4
    diffi
    anim1i
    3adant2
    @5
    cC
    vk
    fsumconst
    syl
    @3
    @7
    @9
    cC
    cmul
    @0
    @1
    @7
    @9
    wceq
    @2
    cA
    cB
    hashdifsn
    3adant3
    oveq1d
    eqtrd
end
