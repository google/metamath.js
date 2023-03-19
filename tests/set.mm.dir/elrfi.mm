include "wcel.mm"
include "cpw.mm"
include "wss.mm"
include "wa.mm"
include "cvv.mm"
include "csn.mm"
include "cun.mm"
include "cfi.mm"
include "cfv.mm"
include "cv.mm"
include "cint.mm"
include "cin.mm"
include "wceq.mm"
include "cfn.mm"
include "wrex.mm"
include "wi.mm"
include "elex.mm"
include "a1i.mm"
include "inex1g.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "rexlimdvw.mm"
include "adantr.mm"
include "wb.mm"
include "simpr.mm"
include "snex.mm"
include "pwexg.mm"
include "ad2antrr.mm"
include "simplr.mm"
include "ssexd.mm"
include "unexg.mm"
include "sylancr.mm"
include "elfi.mm"
include "syl2anc.mm"
include "cdif.mm"
include "inss1.mm"
include "uncom.mm"
include "pweqi.mm"
include "sseqtri.mm"
include "sseli.mm"
include "elpwun.mm"
include "sylib.mm"
include "ad2antrl.mm"
include "inss2.mm"
include "diffi.mm"
include "syl.mm"
include "elind.mm"
include "incom.mm"
include "simprr.mm"
include "cuni.mm"
include "c0.mm"
include "wne.mm"
include "eqeltrrd.mm"
include "intex.mm"
include "sylibr.mm"
include "intssuni.mm"
include "elpwid.mm"
include "pwidg.mm"
include "snssd.mm"
include "unssd.mm"
include "sstrd.mm"
include "sspwuni.mm"
include "eqsstrd.mm"
include "df-ss.mm"
include "syl5req.mm"
include "ineq2.mm"
include "ad2antll.mm"
include "eqtrd.mm"
include "intun.mm"
include "intsng.mm"
include "ineq1d.mm"
include "ad3antrrr.mm"
include "undif2.mm"
include "inteqi.mm"
include "syl6eqr.mm"
include "syl5eq.mm"
include "inteq.mm"
include "ineq2d.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "rexlimdvaa.mm"
include "ssun1.mm"
include "elpwi.mm"
include "ssun4.mm"
include "3syl.mm"
include "adantl.mm"
include "vex.mm"
include "unex.mm"
include "elpw.mm"
include "snfi.mm"
include "unfi.mm"
include "eqcomd.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "bitrd.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem elrfi
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let vw: setvar w

  disjoint A v
  disjoint B v
  disjoint C v
  disjoint V v
  disjoint A w
  disjoint v w
  disjoint B w
  disjoint C w
  disjoint V w
  assert |- ( ( B e. V /\ C C_ ~P B ) -> ( A e. ( fi ` ( { B } u. C ) ) <-> E. v e. ( ~P C i^i Fin ) A = ( B i^i |^| v ) ) )

  proof
    cB
    cV
    wcel
    #
    cC
    cB
    cpw
    #
    wss
    #
    wa
    #
    cA
    cvv
    wcel
    #
    cA
    cB
    csn
    #
    cC
    cun
    #
    cfi
    cfv
    #
    wcel
    #
    cA
    cB
    vv
    cv
    #
    cint
    #
    cin
    #
    wceq
    #
    vv
    cC
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @8
    @4
    wi
    @3
    cA
    @7
    elex
    a1i
    @0
    @15
    @4
    wi
    @2
    @0
    @12
    @4
    vv
    @14
    @0
    @4
    @12
    @11
    cvv
    wcel
    cB
    @10
    cV
    inex1g
    cA
    @11
    cvv
    eleq1
    syl5ibrcom
    rexlimdvw
    adantr
    @3
    @4
    @8
    @15
    wb
    @3
    @4
    wa
    #
    @8
    cA
    vw
    cv
    #
    cint
    #
    wceq
    #
    vw
    @6
    cpw
    #
    cfn
    cin
    #
    wrex
    #
    @15
    @16
    @4
    @6
    cvv
    wcel
    #
    @8
    @22
    wb
    @3
    @4
    simpr
    @16
    @5
    cvv
    wcel
    cC
    cvv
    wcel
    @23
    cB
    snex
    #
    @16
    cC
    @1
    cvv
    @0
    @1
    cvv
    wcel
    @2
    @4
    cB
    cV
    pwexg
    ad2antrr
    @0
    @2
    @4
    simplr
    ssexd
    @5
    cC
    cvv
    cvv
    unexg
    sylancr
    vw
    cA
    @6
    cvv
    cvv
    elfi
    syl2anc
    @16
    @22
    @15
    @16
    @19
    @15
    vw
    @21
    @16
    @17
    @21
    wcel
    #
    @19
    wa
    #
    wa
    #
    @17
    @5
    cdif
    #
    @14
    wcel
    cA
    cB
    @28
    cint
    #
    cin
    #
    wceq
    #
    @15
    @27
    @13
    cfn
    @28
    @25
    @28
    @13
    wcel
    #
    @16
    @19
    @25
    @17
    cC
    @5
    cun
    #
    cpw
    #
    wcel
    @32
    @21
    @34
    @17
    @21
    @20
    @34
    @20
    cfn
    inss1
    #
    @6
    @33
    @5
    cC
    uncom
    pweqi
    sseqtri
    sseli
    @17
    cC
    @5
    @24
    elpwun
    sylib
    ad2antrl
    @25
    @28
    cfn
    wcel
    #
    @16
    @19
    @25
    @17
    cfn
    wcel
    @36
    @21
    cfn
    @17
    @20
    cfn
    inss2
    sseli
    @17
    @5
    diffi
    syl
    ad2antrl
    elind
    @27
    cA
    @5
    @28
    cun
    #
    cint
    #
    @30
    @27
    cA
    @5
    @17
    cun
    #
    cint
    #
    @38
    @27
    cA
    cB
    @18
    cin
    #
    @40
    @27
    cA
    cB
    cA
    cin
    #
    @41
    @27
    @42
    cA
    cB
    cin
    #
    cA
    cB
    cA
    incom
    @27
    cA
    cB
    wss
    @43
    cA
    wceq
    @27
    cA
    @18
    cB
    @16
    @25
    @19
    simprr
    #
    @27
    @18
    @17
    cuni
    #
    cB
    @27
    @17
    c0
    wne
    #
    @18
    @45
    wss
    @27
    @18
    cvv
    wcel
    @46
    @27
    cA
    @18
    cvv
    @44
    @3
    @4
    @26
    simplr
    eqeltrrd
    @17
    intex
    sylibr
    @17
    intssuni
    syl
    @27
    @17
    @1
    wss
    @45
    cB
    wss
    @27
    @17
    @6
    @1
    @25
    @17
    @6
    wss
    @16
    @19
    @25
    @17
    @6
    @21
    @20
    @17
    @35
    sseli
    elpwid
    ad2antrl
    @3
    @6
    @1
    wss
    @4
    @26
    @3
    @5
    cC
    @1
    @0
    @5
    @1
    wss
    @2
    @0
    cB
    @1
    cB
    cV
    pwidg
    snssd
    adantr
    @0
    @2
    simpr
    unssd
    ad2antrr
    sstrd
    @17
    cB
    sspwuni
    sylib
    sstrd
    eqsstrd
    cA
    cB
    df-ss
    sylib
    syl5req
    @19
    @42
    @41
    wceq
    @16
    @25
    cA
    @18
    cB
    ineq2
    ad2antll
    eqtrd
    @0
    @41
    @40
    wceq
    @2
    @4
    @26
    @0
    @40
    @5
    cint
    #
    @18
    cin
    @41
    @5
    @17
    intun
    @0
    @47
    cB
    @18
    cB
    cV
    intsng
    #
    ineq1d
    syl5req
    ad3antrrr
    eqtrd
    @37
    @39
    @5
    @17
    undif2
    inteqi
    syl6eqr
    @0
    @38
    @30
    wceq
    @2
    @4
    @26
    @0
    @38
    @47
    @29
    cin
    @30
    @5
    @28
    intun
    @0
    @47
    cB
    @29
    @48
    ineq1d
    syl5eq
    ad3antrrr
    eqtrd
    @12
    @31
    vv
    @28
    @14
    @9
    @28
    wceq
    #
    @11
    @30
    cA
    @49
    @10
    @29
    cB
    @9
    @28
    inteq
    ineq2d
    eqeq2d
    rspcev
    syl2anc
    rexlimdvaa
    @16
    @12
    @22
    vv
    @14
    @16
    @9
    @14
    wcel
    #
    wa
    #
    @22
    @12
    @11
    @18
    wceq
    #
    vw
    @21
    wrex
    #
    @51
    @5
    @9
    cun
    #
    @21
    wcel
    @11
    @54
    cint
    #
    wceq
    #
    @53
    @51
    @20
    cfn
    @54
    @51
    @54
    @6
    wss
    @54
    @20
    wcel
    @51
    @5
    @9
    @6
    @5
    @6
    wss
    @51
    @5
    cC
    ssun1
    a1i
    @50
    @9
    @6
    wss
    #
    @16
    @50
    @9
    @13
    wcel
    @9
    cC
    wss
    @57
    @14
    @13
    @9
    @13
    cfn
    inss1
    sseli
    @9
    cC
    elpwi
    @9
    cC
    @5
    ssun4
    3syl
    adantl
    unssd
    @54
    @6
    @5
    @9
    @24
    vv
    vex
    unex
    elpw
    sylibr
    @51
    @5
    cfn
    wcel
    @9
    cfn
    wcel
    #
    @54
    cfn
    wcel
    cB
    snfi
    @50
    @58
    @16
    @14
    cfn
    @9
    @13
    cfn
    inss2
    sseli
    adantl
    @5
    @9
    unfi
    sylancr
    elind
    @0
    @56
    @2
    @4
    @50
    @0
    @11
    @47
    @10
    cin
    @55
    @0
    cB
    @47
    @10
    @0
    @47
    cB
    @48
    eqcomd
    ineq1d
    @5
    @9
    intun
    syl6eqr
    ad3antrrr
    @52
    @56
    vw
    @54
    @21
    @17
    @54
    wceq
    @18
    @55
    @11
    @17
    @54
    inteq
    eqeq2d
    rspcev
    syl2anc
    @12
    @19
    @52
    vw
    @21
    cA
    @11
    @18
    eqeq1
    rexbidv
    syl5ibrcom
    rexlimdva
    impbid
    bitrd
    ex
    pm5.21ndd
end
