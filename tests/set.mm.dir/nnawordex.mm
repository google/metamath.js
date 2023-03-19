include "com.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cv.mm"
include "coa.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "con0.mm"
include "crab.mm"
include "cint.mm"
include "simplr.mm"
include "nnon.mm"
include "syl.mm"
include "simpll.mm"
include "nnaword2.mm"
include "syl2anc.mm"
include "oveq2.mm"
include "sseq2d.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "intss1.mm"
include "word.mm"
include "wi.mm"
include "c0.mm"
include "wne.mm"
include "ssrab2.mm"
include "ne0i.mm"
include "oninton.mm"
include "sylancr.mm"
include "eloni.mm"
include "ordom.mm"
include "ordtr2.mm"
include "sylancl.mm"
include "mp2and.mm"
include "csuc.mm"
include "nna0.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "eqsstrd.mm"
include "sseq1d.mm"
include "syl5ibrcom.mm"
include "simprr.mm"
include "oveq2d.mm"
include "adantr.mm"
include "simprl.mm"
include "nnasuc.mm"
include "eqtrd.mm"
include "nnord.mm"
include "wn.mm"
include "vex.mm"
include "sucid.mm"
include "syl5eleqr.mm"
include "onnminsb.mm"
include "sylc.mm"
include "adantl.mm"
include "wb.mm"
include "nnacl.mm"
include "ordtri1.mm"
include "con2bid.mm"
include "mpbird.mm"
include "ordsucss.mm"
include "rexlimdvaa.mm"
include "wo.mm"
include "nn0suc.mm"
include "mpjaod.mm"
include "onint.mm"
include "nfrab1.mm"
include "nfint.mm"
include "nfcv.mm"
include "nfov.mm"
include "nfss.mm"
include "elrabf.mm"
include "simprbi.mm"
include "eqssd.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "ex.mm"
include "nnaword1.mm"
include "adantlr.mm"
include "sseq2.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "impbid.mm"

theorem nnawordex
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. _om /\ B e. _om ) -> ( A C_ B <-> E. x e. _om ( A +o x ) = B ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    wa
    #
    cA
    cB
    wss
    #
    cA
    vx
    cv
    #
    coa
    co
    #
    cB
    wceq
    #
    vx
    com
    wrex
    #
    @2
    @3
    @7
    @2
    @3
    wa
    #
    cB
    cA
    vy
    cv
    #
    coa
    co
    #
    wss
    #
    vy
    con0
    crab
    #
    cint
    #
    com
    wcel
    #
    cA
    @13
    coa
    co
    #
    cB
    wceq
    #
    @7
    @8
    @13
    cB
    wss
    #
    @1
    @14
    @8
    cB
    @12
    wcel
    #
    @17
    @8
    cB
    con0
    wcel
    #
    cB
    cA
    cB
    coa
    co
    #
    wss
    #
    @18
    @8
    @1
    @19
    @0
    @1
    @3
    simplr
    #
    cB
    nnon
    syl
    @8
    @1
    @0
    @21
    @22
    @0
    @1
    @3
    simpll
    #
    cB
    cA
    nnaword2
    syl2anc
    @11
    @21
    vy
    cB
    con0
    @9
    cB
    wceq
    @10
    @20
    cB
    @9
    cB
    cA
    coa
    oveq2
    sseq2d
    elrab
    sylanbrc
    #
    cB
    @12
    intss1
    syl
    @22
    @8
    @13
    word
    #
    com
    word
    @17
    @1
    wa
    @14
    wi
    @8
    @13
    con0
    wcel
    #
    @25
    @8
    @12
    con0
    wss
    #
    @12
    c0
    wne
    #
    @26
    @11
    vy
    con0
    ssrab2
    #
    @8
    @18
    @28
    @24
    @12
    cB
    ne0i
    syl
    #
    @12
    oninton
    sylancr
    @13
    eloni
    syl
    ordom
    @13
    cB
    com
    ordtr2
    sylancl
    mp2and
    #
    @8
    @15
    cB
    @8
    @13
    c0
    wceq
    #
    @15
    cB
    wss
    #
    @13
    @4
    csuc
    #
    wceq
    #
    vx
    com
    wrex
    #
    @8
    @33
    @32
    cA
    c0
    coa
    co
    #
    cB
    wss
    @8
    @37
    cA
    cB
    @0
    @37
    cA
    wceq
    @1
    @3
    cA
    nna0
    ad2antrr
    @2
    @3
    simpr
    eqsstrd
    @32
    @15
    @37
    cB
    @13
    c0
    cA
    coa
    oveq2
    sseq1d
    syl5ibrcom
    @8
    @35
    @33
    vx
    com
    @8
    @4
    com
    wcel
    #
    @35
    wa
    #
    wa
    #
    @15
    @5
    csuc
    #
    cB
    @40
    @15
    cA
    @34
    coa
    co
    #
    @41
    @40
    @13
    @34
    cA
    coa
    @8
    @38
    @35
    simprr
    oveq2d
    @40
    @0
    @38
    @42
    @41
    wceq
    @8
    @0
    @39
    @23
    adantr
    #
    @8
    @38
    @35
    simprl
    #
    cA
    @4
    nnasuc
    syl2anc
    eqtrd
    @40
    cB
    word
    #
    @5
    cB
    wcel
    #
    @41
    cB
    wss
    @8
    @45
    @39
    @8
    @1
    @45
    @22
    cB
    nnord
    syl
    adantr
    #
    @40
    @46
    cB
    @5
    wss
    #
    wn
    #
    @39
    @49
    @8
    @39
    @4
    con0
    wcel
    #
    @4
    @13
    wcel
    @49
    @38
    @50
    @35
    @4
    nnon
    adantr
    @39
    @4
    @34
    @13
    @4
    vx
    vex
    sucid
    @38
    @35
    simpr
    syl5eleqr
    @11
    @48
    vy
    @4
    @9
    @4
    wceq
    @10
    @5
    cB
    @9
    @4
    cA
    coa
    oveq2
    sseq2d
    onnminsb
    sylc
    adantl
    @40
    @48
    @46
    @40
    @45
    @5
    word
    #
    @48
    @46
    wn
    wb
    @47
    @40
    @5
    com
    wcel
    #
    @51
    @40
    @0
    @38
    @52
    @43
    @44
    cA
    @4
    nnacl
    syl2anc
    @5
    nnord
    syl
    cB
    @5
    ordtri1
    syl2anc
    con2bid
    mpbird
    @5
    cB
    ordsucss
    sylc
    eqsstrd
    rexlimdvaa
    @8
    @14
    @32
    @36
    wo
    @31
    vx
    @13
    nn0suc
    syl
    mpjaod
    @8
    @13
    @12
    wcel
    #
    cB
    @15
    wss
    #
    @8
    @27
    @28
    @53
    @29
    @30
    @12
    onint
    sylancr
    @53
    @26
    @54
    @11
    @54
    vy
    @13
    con0
    vy
    @12
    @11
    vy
    con0
    nfrab1
    nfint
    #
    vy
    con0
    nfcv
    vy
    cB
    @15
    vy
    cB
    nfcv
    vy
    cA
    @13
    coa
    vy
    cA
    nfcv
    vy
    coa
    nfcv
    @55
    nfov
    nfss
    @9
    @13
    wceq
    @10
    @15
    cB
    @9
    @13
    cA
    coa
    oveq2
    sseq2d
    elrabf
    simprbi
    syl
    eqssd
    @6
    @16
    vx
    @13
    com
    @4
    @13
    wceq
    @5
    @15
    cB
    @4
    @13
    cA
    coa
    oveq2
    eqeq1d
    rspcev
    syl2anc
    ex
    @2
    @6
    @3
    vx
    com
    @2
    @38
    wa
    cA
    @5
    wss
    #
    @6
    @3
    @0
    @38
    @56
    @1
    cA
    @4
    nnaword1
    adantlr
    @5
    cB
    cA
    sseq2
    syl5ibcom
    rexlimdva
    impbid
end
