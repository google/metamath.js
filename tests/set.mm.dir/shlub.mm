include "csh.mm"
include "wcel.mm"
include "cch.mm"
include "w3a.mm"
include "wss.mm"
include "wa.mm"
include "chj.mm"
include "co.mm"
include "cun.mm"
include "cort.mm"
include "cfv.mm"
include "unss.mm"
include "chil.mm"
include "wi.mm"
include "simp1.mm"
include "shss.mm"
include "syl.mm"
include "simp2.mm"
include "unssd.mm"
include "chss.mm"
include "3ad2ant3.mm"
include "occon2.mm"
include "syl2anc.mm"
include "syl5bi.mm"
include "wceq.mm"
include "shjval.mm"
include "ococ.mm"
include "eqcomd.mm"
include "sseq12d.mm"
include "sylibrd.mm"
include "shub1.mm"
include "sstr.mm"
include "sylan.mm"
include "shub2.mm"
include "jca.mm"
include "ex.mm"
include "impbid.mm"

theorem shlub
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. SH /\ B e. SH /\ C e. CH ) -> ( ( A C_ C /\ B C_ C ) <-> ( A vH B ) C_ C ) )

  proof
    cA
    csh
    wcel
    #
    cB
    csh
    wcel
    #
    cC
    cch
    wcel
    #
    w3a
    #
    cA
    cC
    wss
    #
    cB
    cC
    wss
    #
    wa
    #
    cA
    cB
    chj
    co
    #
    cC
    wss
    #
    @3
    @6
    cA
    cB
    cun
    #
    cort
    cfv
    cort
    cfv
    #
    cC
    cort
    cfv
    cort
    cfv
    #
    wss
    #
    @8
    @6
    @9
    cC
    wss
    #
    @3
    @12
    cA
    cB
    cC
    unss
    @3
    @9
    chil
    wss
    cC
    chil
    wss
    #
    @13
    @12
    wi
    @3
    cA
    cB
    chil
    @3
    @0
    cA
    chil
    wss
    @0
    @1
    @2
    simp1
    #
    cA
    shss
    syl
    @3
    @1
    cB
    chil
    wss
    @0
    @1
    @2
    simp2
    #
    cB
    shss
    syl
    unssd
    @2
    @0
    @14
    @1
    cC
    chss
    3ad2ant3
    @9
    cC
    occon2
    syl2anc
    syl5bi
    @3
    @7
    @10
    cC
    @11
    @3
    @0
    @1
    @7
    @10
    wceq
    @15
    @16
    cA
    cB
    shjval
    syl2anc
    @3
    @11
    cC
    @2
    @0
    @11
    cC
    wceq
    @1
    cC
    ococ
    3ad2ant3
    eqcomd
    sseq12d
    sylibrd
    @3
    @8
    @6
    @3
    @8
    wa
    @4
    @5
    @3
    cA
    @7
    wss
    #
    @8
    @4
    @3
    @0
    @1
    @17
    @15
    @16
    cA
    cB
    shub1
    syl2anc
    cA
    @7
    cC
    sstr
    sylan
    @3
    cB
    @7
    wss
    #
    @8
    @5
    @3
    @1
    @0
    @18
    @16
    @15
    cB
    cA
    shub2
    syl2anc
    cB
    @7
    cC
    sstr
    sylan
    jca
    ex
    impbid
end
