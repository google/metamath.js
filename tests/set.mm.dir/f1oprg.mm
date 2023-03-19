include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "cop.mm"
include "wf1o.mm"
include "csn.mm"
include "cun.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "f1osng.mm"
include "ad2antrr.mm"
include "ad2antlr.mm"
include "disjsn2.mm"
include "ad2antrl.mm"
include "ad2antll.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "df-pr.mm"
include "eqcomi.mm"
include "a1i.mm"
include "f1oeq123d.mm"
include "mpbid.mm"
include "ex.mm"

theorem f1oprg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) ) -> ( ( A =/= C /\ B =/= D ) -> { <. A , B >. , <. C , D >. } : { A , C } -1-1-onto-> { B , D } ) )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cC
    cX
    wcel
    cD
    cY
    wcel
    wa
    #
    wa
    #
    cA
    cC
    wne
    #
    cB
    cD
    wne
    #
    wa
    #
    cA
    cC
    cpr
    #
    cB
    cD
    cpr
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cpr
    #
    wf1o
    #
    @2
    @5
    wa
    #
    cA
    csn
    #
    cC
    csn
    #
    cun
    #
    cB
    csn
    #
    cD
    csn
    #
    cun
    #
    @8
    csn
    #
    @9
    csn
    #
    cun
    #
    wf1o
    #
    @11
    @12
    @13
    @16
    @19
    wf1o
    #
    @14
    @17
    @20
    wf1o
    #
    @13
    @14
    cin
    c0
    wceq
    #
    @16
    @17
    cin
    c0
    wceq
    #
    @22
    @0
    @23
    @1
    @5
    cA
    cB
    cV
    cW
    f1osng
    ad2antrr
    @1
    @24
    @0
    @5
    cC
    cD
    cX
    cY
    f1osng
    ad2antlr
    @3
    @25
    @2
    @4
    cA
    cC
    disjsn2
    ad2antrl
    @4
    @26
    @2
    @3
    cB
    cD
    disjsn2
    ad2antll
    @13
    @16
    @14
    @17
    @19
    @20
    f1oun
    syl22anc
    @12
    @15
    @6
    @18
    @7
    @21
    @10
    @21
    @10
    wceq
    @12
    @10
    @21
    @8
    @9
    df-pr
    eqcomi
    a1i
    @15
    @6
    wceq
    @12
    @6
    @15
    cA
    cC
    df-pr
    eqcomi
    a1i
    @18
    @7
    wceq
    @12
    @7
    @18
    cB
    cD
    df-pr
    eqcomi
    a1i
    f1oeq123d
    mpbid
    ex
end
