include "c0.mm"
include "wne.mm"
include "crpss.mm"
include "wor.mm"
include "wa.mm"
include "cfn.mm"
include "wcel.mm"
include "cuni.mm"
include "wss.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "csn.mm"
include "cun.mm"
include "wceq.mm"
include "sseq1.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "imbi2d.mm"
include "wral.mm"
include "0ss.mm"
include "rgenw.mm"
include "r19.2z.mm"
include "mpan2.mm"
include "adantr.mm"
include "a1d.mm"
include "id.mm"
include "unssad.mm"
include "imim1i.mm"
include "sseq2.mm"
include "cbvrexv.mm"
include "simpr.mm"
include "unssbd.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "eluni2.mm"
include "sylib.mm"
include "reeanv.mm"
include "simpllr.mm"
include "simprlr.mm"
include "simprll.mm"
include "sorpssun.mm"
include "syl12anc.mm"
include "simprrr.mm"
include "simprrl.mm"
include "snssd.mm"
include "unss12.mm"
include "syl2anc.mm"
include "rspcev.mm"
include "expr.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "mpand.mm"
include "syl5bi.mm"
include "ex.mm"
include "a2d.mm"
include "syl5.mm"
include "a2i.mm"
include "a1i.mm"
include "findcard2.mm"
include "com12.mm"
include "imp32.mm"

theorem finsschain
  let vz: setvar z
  let cA: class A
  let cB: class B
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vu: setvar u
  let vw: setvar w

  disjoint A z
  disjoint B z
  disjoint a b
  disjoint a c
  disjoint a u
  disjoint a w
  disjoint a z
  disjoint A a
  disjoint b c
  disjoint b u
  disjoint b w
  disjoint b z
  disjoint A b
  disjoint c u
  disjoint c w
  disjoint c z
  disjoint A c
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint w z
  disjoint A w
  disjoint B a
  disjoint B b
  disjoint B c
  assert |- ( ( ( A =/= (/) /\ [C.] Or A ) /\ ( B e. Fin /\ B C_ U. A ) ) -> E. z e. A B C_ z )

  proof
    cA
    c0
    wne
    #
    cA
    crpss
    wor
    #
    wa
    #
    cB
    cfn
    wcel
    #
    cB
    cA
    cuni
    #
    wss
    #
    cB
    vz
    cv
    #
    wss
    #
    vz
    cA
    wrex
    #
    @3
    @2
    @5
    @8
    wi
    #
    @2
    va
    cv
    #
    @4
    wss
    #
    @10
    @6
    wss
    #
    vz
    cA
    wrex
    #
    wi
    #
    wi
    @2
    c0
    @4
    wss
    #
    c0
    @6
    wss
    #
    vz
    cA
    wrex
    #
    wi
    #
    wi
    @2
    vb
    cv
    #
    @4
    wss
    #
    @19
    @6
    wss
    #
    vz
    cA
    wrex
    #
    wi
    #
    wi
    #
    @2
    @19
    vc
    cv
    #
    csn
    #
    cun
    #
    @4
    wss
    #
    @27
    @6
    wss
    #
    vz
    cA
    wrex
    #
    wi
    #
    wi
    #
    @2
    @9
    wi
    va
    vb
    vc
    cB
    @10
    c0
    wceq
    #
    @14
    @18
    @2
    @33
    @11
    @15
    @13
    @17
    @10
    c0
    @4
    sseq1
    @33
    @12
    @16
    vz
    cA
    @10
    c0
    @6
    sseq1
    rexbidv
    imbi12d
    imbi2d
    @10
    @19
    wceq
    #
    @14
    @23
    @2
    @34
    @11
    @20
    @13
    @22
    @10
    @19
    @4
    sseq1
    @34
    @12
    @21
    vz
    cA
    @10
    @19
    @6
    sseq1
    rexbidv
    imbi12d
    imbi2d
    @10
    @27
    wceq
    #
    @14
    @31
    @2
    @35
    @11
    @28
    @13
    @30
    @10
    @27
    @4
    sseq1
    @35
    @12
    @29
    vz
    cA
    @10
    @27
    @6
    sseq1
    rexbidv
    imbi12d
    imbi2d
    @10
    cB
    wceq
    #
    @14
    @9
    @2
    @36
    @11
    @5
    @13
    @8
    @10
    cB
    @4
    sseq1
    @36
    @12
    @7
    vz
    cA
    @10
    cB
    @6
    sseq1
    rexbidv
    imbi12d
    imbi2d
    @2
    @17
    @15
    @0
    @17
    @1
    @0
    @16
    vz
    cA
    wral
    @17
    @16
    vz
    cA
    @6
    0ss
    rgenw
    @16
    vz
    cA
    r19.2z
    mpan2
    adantr
    a1d
    @24
    @32
    wi
    @19
    cfn
    wcel
    @2
    @23
    @31
    @23
    @28
    @22
    wi
    @2
    @31
    @28
    @20
    @22
    @28
    @19
    @26
    @4
    @28
    id
    unssad
    imim1i
    @2
    @28
    @22
    @30
    @2
    @28
    @22
    @30
    wi
    @22
    @19
    vw
    cv
    #
    wss
    #
    vw
    cA
    wrex
    #
    @2
    @28
    wa
    #
    @30
    @21
    @38
    vz
    vw
    cA
    @6
    @37
    @19
    sseq2
    cbvrexv
    @40
    @25
    vu
    cv
    #
    wcel
    #
    vu
    cA
    wrex
    #
    @39
    @30
    @40
    @25
    @4
    wcel
    #
    @43
    @40
    @26
    @4
    wss
    @44
    @40
    @19
    @26
    @4
    @2
    @28
    simpr
    unssbd
    @25
    @4
    vc
    vex
    snss
    sylibr
    vu
    @25
    cA
    eluni2
    sylib
    @43
    @39
    wa
    @42
    @38
    wa
    #
    vw
    cA
    wrex
    vu
    cA
    wrex
    @40
    @30
    @42
    @38
    vu
    vw
    cA
    cA
    reeanv
    @40
    @45
    @30
    vu
    vw
    cA
    cA
    @40
    @41
    cA
    wcel
    #
    @37
    cA
    wcel
    #
    wa
    #
    @45
    @30
    @40
    @48
    @45
    wa
    #
    wa
    #
    @37
    @41
    cun
    #
    cA
    wcel
    #
    @27
    @51
    wss
    #
    @30
    @50
    @1
    @47
    @46
    @52
    @0
    @1
    @28
    @49
    simpllr
    @40
    @46
    @47
    @45
    simprlr
    @40
    @46
    @47
    @45
    simprll
    cA
    @37
    @41
    sorpssun
    syl12anc
    @50
    @38
    @26
    @41
    wss
    @53
    @40
    @48
    @42
    @38
    simprrr
    @50
    @25
    @41
    @40
    @48
    @42
    @38
    simprrl
    snssd
    @19
    @37
    @26
    @41
    unss12
    syl2anc
    @29
    @53
    vz
    @51
    cA
    @6
    @51
    @27
    sseq2
    rspcev
    syl2anc
    expr
    rexlimdvva
    syl5bir
    mpand
    syl5bi
    ex
    a2d
    syl5
    a2i
    a1i
    findcard2
    com12
    imp32
end
