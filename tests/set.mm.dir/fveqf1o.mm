include "wf1o.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "cid.mm"
include "ccnv.mm"
include "cpr.mm"
include "cdif.mm"
include "cres.mm"
include "cop.mm"
include "cun.mm"
include "ccom.mm"
include "simp1.mm"
include "cin.mm"
include "c0.mm"
include "f1oi.mm"
include "a1i.mm"
include "simp2.mm"
include "wf.mm"
include "f1ocnv.mm"
include "f1of.mm"
include "3syl.mm"
include "simp3.mm"
include "ffvelrnd.mm"
include "f1oprswap.mm"
include "syl2anc.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "wb.mm"
include "uncom.mm"
include "wss.mm"
include "prssi.mm"
include "undif.mm"
include "sylib.mm"
include "syl5eq.mm"
include "f1oeq2.mm"
include "syl.mm"
include "mpbid.mm"
include "f1oeq3.mm"
include "f1oco.mm"
include "f1oeq1.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "fveq1i.mm"
include "fvco3.mm"
include "wfn.mm"
include "fnresi.mm"
include "f1ofn.mm"
include "prid1g.mm"
include "fvun2.mm"
include "syl112anc.mm"
include "wfun.mm"
include "f1ofun.mm"
include "opex.mm"
include "prid1.mm"
include "funopfv.mm"
include "mpisyl.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "f1ocnvfv2.mm"
include "jca.mm"

theorem fveqf1o
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cG: class G
  assume fveqf1o.1: |- G = ( F o. ( ( _I |` ( A \ { C , ( `' F ` D ) } ) ) u. { <. C , ( `' F ` D ) >. , <. ( `' F ` D ) , C >. } ) )


  assert |- ( ( F : A -1-1-onto-> B /\ C e. A /\ D e. B ) -> ( G : A -1-1-onto-> B /\ ( G ` C ) = D ) )

  proof
    cA
    cB
    cF
    wf1o
    #
    cC
    cA
    wcel
    #
    cD
    cB
    wcel
    #
    w3a
    #
    cA
    cB
    cG
    wf1o
    #
    cC
    cG
    cfv
    #
    cD
    wceq
    @3
    cA
    cB
    cF
    cid
    cA
    cC
    cD
    cF
    ccnv
    #
    cfv
    #
    cpr
    #
    cdif
    #
    cres
    #
    cC
    @7
    cop
    #
    @7
    cC
    cop
    #
    cpr
    #
    cun
    #
    ccom
    #
    wf1o
    #
    @4
    @3
    @0
    cA
    cA
    @14
    wf1o
    #
    @16
    @0
    @1
    @2
    simp1
    #
    @3
    cA
    @9
    @8
    cun
    #
    @14
    wf1o
    #
    @17
    @3
    @19
    @19
    @14
    wf1o
    #
    @20
    @3
    @9
    @9
    @10
    wf1o
    #
    @8
    @8
    @13
    wf1o
    #
    @9
    @8
    cin
    #
    c0
    wceq
    #
    @25
    @21
    @22
    @3
    @9
    f1oi
    a1i
    @3
    @1
    @7
    cA
    wcel
    #
    @23
    @0
    @1
    @2
    simp2
    #
    @3
    cB
    cA
    cD
    @6
    @3
    @0
    cB
    cA
    @6
    wf1o
    cB
    cA
    @6
    wf
    @18
    cA
    cB
    cF
    f1ocnv
    cB
    cA
    @6
    f1of
    3syl
    @0
    @1
    @2
    simp3
    #
    ffvelrnd
    #
    cC
    @7
    cA
    cA
    f1oprswap
    syl2anc
    #
    @25
    @3
    @24
    @8
    @9
    cin
    c0
    @9
    @8
    incom
    @8
    cA
    disjdif
    eqtri
    a1i
    #
    @31
    @9
    @9
    @8
    @8
    @10
    @13
    f1oun
    syl22anc
    @3
    @19
    cA
    wceq
    #
    @21
    @20
    wb
    @3
    @19
    @8
    @9
    cun
    #
    cA
    @9
    @8
    uncom
    @3
    @8
    cA
    wss
    #
    @33
    cA
    wceq
    @3
    @1
    @26
    @34
    @27
    @29
    cC
    @7
    cA
    prssi
    syl2anc
    @8
    cA
    undif
    sylib
    syl5eq
    #
    @19
    cA
    @19
    @14
    f1oeq2
    syl
    mpbid
    @3
    @32
    @20
    @17
    wb
    @35
    @19
    cA
    cA
    @14
    f1oeq3
    syl
    mpbid
    #
    cA
    cA
    cB
    cF
    @14
    f1oco
    syl2anc
    cG
    @15
    wceq
    @4
    @16
    wb
    fveqf1o.1
    cA
    cB
    cG
    @15
    f1oeq1
    ax-mp
    sylibr
    @3
    @5
    cC
    @14
    cfv
    #
    cF
    cfv
    #
    cD
    @3
    @5
    cC
    @15
    cfv
    #
    @38
    cC
    cG
    @15
    fveqf1o.1
    fveq1i
    @3
    cA
    cA
    @14
    wf
    #
    @1
    @39
    @38
    wceq
    @3
    @17
    @40
    @36
    cA
    cA
    @14
    f1of
    syl
    @27
    cA
    cA
    cC
    cF
    @14
    fvco3
    syl2anc
    syl5eq
    @3
    @38
    @7
    cF
    cfv
    #
    cD
    @3
    @37
    @7
    cF
    @3
    @37
    cC
    @13
    cfv
    #
    @7
    @3
    @10
    @9
    wfn
    #
    @13
    @8
    wfn
    #
    @25
    cC
    @8
    wcel
    #
    @37
    @42
    wceq
    @43
    @3
    @9
    fnresi
    a1i
    @3
    @23
    @44
    @30
    @8
    @8
    @13
    f1ofn
    syl
    @31
    @3
    @1
    @45
    @27
    cC
    @7
    cA
    prid1g
    syl
    @9
    @8
    @10
    @13
    cC
    fvun2
    syl112anc
    @3
    @13
    wfun
    #
    @11
    @13
    wcel
    @42
    @7
    wceq
    @3
    @23
    @46
    @30
    @8
    @8
    @13
    f1ofun
    syl
    @11
    @12
    cC
    @7
    opex
    prid1
    cC
    @7
    @13
    funopfv
    mpisyl
    eqtrd
    fveq2d
    @3
    @0
    @2
    @41
    cD
    wceq
    @18
    @28
    cA
    cB
    cD
    cF
    f1ocnvfv2
    syl2anc
    eqtrd
    eqtrd
    jca
end
