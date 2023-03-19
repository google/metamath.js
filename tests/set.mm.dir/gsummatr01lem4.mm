include "ccmn.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "csn.mm"
include "cdif.mm"
include "cfv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "wi.mm"
include "cvv.mm"
include "eqidd.mm"
include "weq.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantr.mm"
include "adantl.mm"
include "ifbid.mm"
include "oveq12.mm"
include "ifbieq12d.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "sylan9eqr.mm"
include "eldifi.mm"
include "gsummatr01lem1.mm"
include "sylan2.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "ex.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "simpr.mm"
include "wne.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "simpll.mm"
include "csymg.mm"
include "eqid.mm"
include "symgfv.mm"
include "syl2an.mm"
include "simplrr.mm"
include "3jca.mm"
include "simpllr.mm"
include "symgfvne.mm"
include "syl3c.mm"
include "jca.mm"
include "exp42.mm"
include "sylbi.mm"
include "com13.mm"
include "3imp.mm"
include "eldifsn.mm"
include "sylibr.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfcv.mm"
include "nfel2.mm"
include "nfan.mm"
include "nf3an.mm"
include "nfra2.mm"
include "ovmpt2dxf.mm"
include "eqtr4d.mm"

theorem gsummatr01lem4
  let cA: class A
  let cB: class B
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cL: class L
  let cN: class N
  let c.0: class .0.
  let vr: setvar r
  let cX: class X
  assume gsummatr01.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume gsummatr01.r: |- R = { r e. P | ( r ` K ) = L }
  assume gsummatr01.0: |- .0. = ( 0g ` G )
  assume gsummatr01.s: |- S = ( Base ` G )

  disjoint A i
  disjoint A j
  disjoint A n
  disjoint i j
  disjoint i n
  disjoint j n
  disjoint B i
  disjoint B j
  disjoint B n
  disjoint G i
  disjoint G j
  disjoint G n
  disjoint K i
  disjoint K j
  disjoint K n
  disjoint K r
  disjoint L i
  disjoint L j
  disjoint L n
  disjoint L r
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint P r
  disjoint Q r
  disjoint Q i
  disjoint Q j
  disjoint Q n
  disjoint R i
  disjoint R j
  disjoint R n
  disjoint S i
  disjoint S j
  disjoint S n
  disjoint .0. i
  disjoint .0. j
  disjoint .0. n
  disjoint X i
  disjoint X j
  assert |- ( ( ( ( G e. CMnd /\ N e. Fin ) /\ ( A. i e. N A. j e. N ( i A j ) e. S /\ B e. S ) /\ ( K e. N /\ L e. N /\ Q e. R ) ) /\ n e. ( N \ { K } ) ) -> ( n ( i e. N , j e. N |-> if ( i = K , if ( j = L , .0. , B ) , ( i A j ) ) ) ( Q ` n ) ) = ( n ( i e. ( N \ { K } ) , j e. ( N \ { L } ) |-> ( i A j ) ) ( Q ` n ) ) )

  proof
    cG
    ccmn
    wcel
    cN
    cfn
    wcel
    wa
    #
    vi
    cv
    #
    vj
    cv
    #
    cA
    co
    #
    cS
    wcel
    #
    vj
    cN
    wral
    #
    vi
    cN
    wral
    #
    cB
    cS
    wcel
    #
    wa
    #
    cK
    cN
    wcel
    #
    cL
    cN
    wcel
    #
    cQ
    cR
    wcel
    #
    w3a
    #
    w3a
    #
    vn
    cv
    #
    cN
    cK
    csn
    #
    cdif
    #
    wcel
    #
    wa
    #
    @14
    @14
    cQ
    cfv
    #
    vi
    vj
    cN
    cN
    @1
    cK
    wceq
    #
    @2
    cL
    wceq
    #
    c.0
    cB
    cif
    #
    @3
    cif
    #
    cmpt2
    #
    co
    #
    @14
    @19
    cA
    co
    #
    @14
    @19
    vi
    vj
    @16
    cN
    cL
    csn
    cdif
    #
    @3
    cmpt2
    #
    co
    @13
    @17
    @25
    @26
    wceq
    #
    @12
    @0
    @17
    @29
    wi
    #
    @8
    @11
    @9
    @30
    @10
    @11
    @17
    @29
    @11
    @17
    wa
    #
    vi
    vj
    @14
    @19
    cN
    cN
    @23
    @26
    @24
    cvv
    @31
    @24
    eqidd
    vi
    vn
    weq
    #
    @2
    @19
    wceq
    #
    wa
    #
    @31
    @23
    @14
    cK
    wceq
    #
    @19
    cL
    wceq
    #
    c.0
    cB
    cif
    #
    @26
    cif
    #
    @26
    @34
    @20
    @35
    @22
    @3
    @37
    @26
    @32
    @20
    @35
    wb
    @33
    @1
    @14
    cK
    eqeq1
    adantr
    @34
    @21
    @36
    c.0
    cB
    @33
    @21
    @36
    wb
    @32
    @2
    @19
    cL
    eqeq1
    adantl
    ifbid
    @1
    @14
    @2
    @19
    cA
    oveq12
    #
    ifbieq12d
    @17
    @38
    @26
    wceq
    @11
    @17
    @35
    @37
    @26
    @17
    @14
    cK
    @14
    cN
    cK
    eldifsni
    #
    neneqd
    iffalsed
    adantl
    sylan9eqr
    @17
    @14
    cN
    wcel
    #
    @11
    @14
    cN
    @15
    eldifi
    #
    adantl
    @17
    @11
    @41
    @19
    cN
    wcel
    #
    @42
    cP
    cQ
    cR
    cK
    cL
    cN
    @14
    vr
    gsummatr01.p
    gsummatr01.r
    gsummatr01lem1
    sylan2
    @31
    @14
    @19
    cA
    ovexd
    ovmpt2d
    ex
    3ad2ant3
    3ad2ant3
    imp
    @18
    vi
    vj
    @14
    @19
    @16
    @27
    @3
    @26
    @28
    @27
    cvv
    @18
    @28
    eqidd
    @34
    @3
    @26
    wceq
    @18
    @39
    adantl
    @18
    @32
    wa
    @27
    eqidd
    @13
    @17
    simpr
    @18
    @43
    @19
    cL
    wne
    #
    wa
    #
    @19
    @27
    wcel
    @13
    @17
    @45
    @12
    @0
    @17
    @45
    wi
    #
    @8
    @9
    @10
    @11
    @46
    @11
    @10
    @9
    @46
    @11
    cQ
    cP
    wcel
    #
    cK
    cQ
    cfv
    #
    cL
    wceq
    #
    wa
    #
    @10
    @9
    @46
    wi
    wi
    cK
    vr
    cv
    #
    cfv
    #
    cL
    wceq
    @49
    vr
    cQ
    cP
    cR
    @51
    cQ
    wceq
    @52
    @48
    cL
    cK
    @51
    cQ
    fveq1
    eqeq1d
    gsummatr01.r
    elrab2
    @50
    @10
    @9
    @17
    @45
    @50
    @10
    @9
    wa
    #
    wa
    #
    @17
    wa
    #
    @43
    @44
    @54
    @47
    @41
    @43
    @17
    @47
    @49
    @53
    simpll
    #
    @42
    cN
    cP
    cQ
    cN
    csymg
    cfv
    #
    @14
    @57
    eqid
    #
    gsummatr01.p
    symgfv
    syl2an
    @55
    @47
    @9
    @41
    w3a
    @49
    @14
    cK
    wne
    #
    @44
    @55
    @47
    @9
    @41
    @54
    @47
    @17
    @56
    adantr
    @50
    @10
    @9
    @17
    simplrr
    @17
    @41
    @54
    @42
    adantl
    3jca
    @47
    @49
    @53
    @17
    simpllr
    @17
    @59
    @54
    @40
    adantl
    cN
    cP
    cQ
    @57
    cK
    @14
    cL
    @58
    gsummatr01.p
    symgfvne
    syl3c
    jca
    exp42
    sylbi
    com13
    3imp
    3ad2ant3
    imp
    @19
    cN
    cL
    eldifsn
    sylibr
    @18
    @14
    @19
    cA
    ovexd
    @13
    @17
    vi
    @0
    @8
    @12
    vi
    @0
    vi
    nfv
    @6
    @7
    vi
    @5
    vi
    cN
    nfra1
    vi
    cB
    cS
    vi
    cS
    nfcv
    nfel2
    nfan
    @12
    vi
    nfv
    nf3an
    vi
    @14
    @16
    vi
    @16
    nfcv
    nfel2
    nfan
    @13
    @17
    vj
    @0
    @8
    @12
    vj
    @0
    vj
    nfv
    @6
    @7
    vj
    @4
    vi
    vj
    cN
    cN
    nfra2
    vj
    cB
    cS
    vj
    cS
    nfcv
    nfel2
    nfan
    @12
    vj
    nfv
    nf3an
    vj
    @14
    @16
    vj
    @16
    nfcv
    nfel2
    nfan
    vj
    @14
    nfcv
    vi
    @19
    nfcv
    vi
    @26
    nfcv
    vj
    @26
    nfcv
    ovmpt2dxf
    eqtr4d
end
