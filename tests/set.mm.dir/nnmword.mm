include "com.mm"
include "wcel.mm"
include "w3a.mm"
include "c0.mm"
include "wa.mm"
include "wn.mm"
include "comu.mm"
include "co.mm"
include "wss.mm"
include "iba.mm"
include "wb.mm"
include "nnmord.mm"
include "3com12.mm"
include "sylan9bbr.mm"
include "notbid.mm"
include "con0.mm"
include "simpl1.mm"
include "nnon.mm"
include "syl.mm"
include "simpl2.mm"
include "ontri1.mm"
include "syl2anc.mm"
include "simpl3.mm"
include "nnmcl.mm"
include "3bitr4d.mm"

theorem nnmword
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. _om /\ B e. _om /\ C e. _om ) /\ (/) e. C ) -> ( A C_ B <-> ( C .o A ) C_ ( C .o B ) ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    cC
    com
    wcel
    #
    w3a
    #
    c0
    cC
    wcel
    #
    wa
    #
    cB
    cA
    wcel
    #
    wn
    #
    cC
    cB
    comu
    co
    #
    cC
    cA
    comu
    co
    #
    wcel
    #
    wn
    #
    cA
    cB
    wss
    #
    @9
    @8
    wss
    #
    @5
    @6
    @10
    @4
    @6
    @6
    @4
    wa
    #
    @3
    @10
    @4
    @6
    iba
    @1
    @0
    @2
    @14
    @10
    wb
    cB
    cA
    cC
    nnmord
    3com12
    sylan9bbr
    notbid
    @5
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    @12
    @7
    wb
    @5
    @0
    @15
    @0
    @1
    @2
    @4
    simpl1
    #
    cA
    nnon
    syl
    @5
    @1
    @16
    @0
    @1
    @2
    @4
    simpl2
    #
    cB
    nnon
    syl
    cA
    cB
    ontri1
    syl2anc
    @5
    @9
    con0
    wcel
    #
    @8
    con0
    wcel
    #
    @13
    @11
    wb
    @5
    @9
    com
    wcel
    #
    @19
    @5
    @2
    @0
    @21
    @0
    @1
    @2
    @4
    simpl3
    #
    @17
    cC
    cA
    nnmcl
    syl2anc
    @9
    nnon
    syl
    @5
    @8
    com
    wcel
    #
    @20
    @5
    @2
    @1
    @23
    @22
    @18
    cC
    cB
    nnmcl
    syl2anc
    @8
    nnon
    syl
    @9
    @8
    ontri1
    syl2anc
    3bitr4d
end
