include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "w3a.mm"
include "cin.mm"
include "cnt.mm"
include "wss.mm"
include "wa.mm"
include "simpr.mm"
include "cuni.mm"
include "wb.mm"
include "simpl.mm"
include "eqid.mm"
include "neiss2.mm"
include "neii1.mm"
include "neiint.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "ssinss1.mm"
include "syl.mm"
include "3adant3.mm"
include "inss2.mm"
include "3adant2.mm"
include "syl5ss.mm"
include "ssind.mm"
include "wceq.mm"
include "simp1.mm"
include "ntrin.mm"
include "sseqtr4d.mm"
include "mpbird.mm"

theorem neiin
  let cA: class A
  let cB: class B
  let cJ: class J
  let cM: class M
  let cN: class N


  assert |- ( ( J e. Top /\ M e. ( ( nei ` J ) ` A ) /\ N e. ( ( nei ` J ) ` B ) ) -> ( M i^i N ) e. ( ( nei ` J ) ` ( A i^i B ) ) )

  proof
    cJ
    ctop
    wcel
    #
    cM
    cA
    cJ
    cnei
    cfv
    #
    cfv
    wcel
    #
    cN
    cB
    @1
    cfv
    wcel
    #
    w3a
    #
    cM
    cN
    cin
    #
    cA
    cB
    cin
    #
    @1
    cfv
    wcel
    #
    @6
    @5
    cJ
    cnt
    cfv
    #
    cfv
    #
    wss
    #
    @4
    @6
    cM
    @8
    cfv
    #
    cN
    @8
    cfv
    #
    cin
    #
    @9
    @4
    @6
    @11
    @12
    @0
    @2
    @6
    @11
    wss
    #
    @3
    @0
    @2
    wa
    #
    cA
    @11
    wss
    #
    @14
    @15
    @2
    @16
    @0
    @2
    simpr
    @15
    @0
    cA
    cJ
    cuni
    #
    wss
    #
    cM
    @17
    wss
    #
    @2
    @16
    wb
    @0
    @2
    simpl
    #
    cA
    cJ
    cM
    @17
    @17
    eqid
    #
    neiss2
    #
    cA
    cJ
    cM
    @17
    @21
    neii1
    #
    cA
    cJ
    cM
    @17
    @21
    neiint
    syl3anc
    mpbid
    cA
    cB
    @11
    ssinss1
    syl
    3adant3
    @4
    @6
    cB
    @12
    cA
    cB
    inss2
    @0
    @3
    cB
    @12
    wss
    #
    @2
    @0
    @3
    wa
    #
    @3
    @24
    @0
    @3
    simpr
    @25
    @0
    cB
    @17
    wss
    cN
    @17
    wss
    #
    @3
    @24
    wb
    @0
    @3
    simpl
    cB
    cJ
    cN
    @17
    @21
    neiss2
    cB
    cJ
    cN
    @17
    @21
    neii1
    #
    cB
    cJ
    cN
    @17
    @21
    neiint
    syl3anc
    mpbid
    3adant2
    syl5ss
    ssind
    @4
    @0
    @19
    @26
    @9
    @13
    wceq
    @0
    @2
    @3
    simp1
    @0
    @2
    @19
    @3
    @23
    3adant3
    @0
    @3
    @26
    @2
    @27
    3adant2
    cM
    cN
    cJ
    @17
    @21
    ntrin
    syl3anc
    sseqtr4d
    @0
    @2
    @7
    @10
    wb
    #
    @3
    @15
    @0
    @6
    @17
    wss
    #
    @5
    @17
    wss
    #
    @28
    @20
    @15
    @18
    @29
    @22
    cA
    cB
    @17
    ssinss1
    syl
    @15
    @19
    @30
    @23
    cM
    cN
    @17
    ssinss1
    syl
    @6
    cJ
    @5
    @17
    @21
    neiint
    syl3anc
    3adant3
    mpbird
end
