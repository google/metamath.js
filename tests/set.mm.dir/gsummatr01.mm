include "ccmn.mm"
include "wcel.mm"
include "cfn.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "w3a.mm"
include "cfv.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "cgsu.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "cplusg.mm"
include "difsnid.mm"
include "eqcomd.mm"
include "3ad2ant1.mm"
include "3ad2ant3.mm"
include "mpteq1d.mm"
include "oveq2d.mm"
include "gsummatr01lem3.mm"
include "cvv.mm"
include "eqidd.mm"
include "wb.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "elrab2.mm"
include "eqeq2.mm"
include "adantl.mm"
include "anbi2d.mm"
include "sylbi.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "syl6bi.mm"
include "imp.mm"
include "simp1.mm"
include "gsummatr01lem1.mm"
include "ancoms.mm"
include "3adant2.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ovmpt2d.mm"
include "cmnd.mm"
include "cbs.mm"
include "cmnmnd.mm"
include "adantr.mm"
include "eqid.mm"
include "simp1l.mm"
include "diffi.mm"
include "weq.mm"
include "eqeq1.mm"
include "ifbid.mm"
include "oveq12.mm"
include "ifbieq12d.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "sylan9eqr.mm"
include "eldifi.mm"
include "simp3.mm"
include "syl2an.mm"
include "ovexd.mm"
include "3ad2antl3.mm"
include "wi.mm"
include "eleq2i.mm"
include "2ralbii.mm"
include "gsummatr01lem2.mm"
include "syl5bi.mm"
include "syl2anr.mm"
include "ex.mm"
include "com13.mm"
include "3adant1.mm"
include "eqeltrd.mm"
include "ralrimiva.mm"
include "gsummptcl.mm"
include "mndrid.mm"
include "syl2anc.mm"
include "gsummatr01lem4.mm"
include "mpteq2dva.mm"
include "3eqtrd.mm"

theorem gsummatr01
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
  assert |- ( ( ( G e. CMnd /\ N e. Fin ) /\ ( A. i e. N A. j e. N ( i A j ) e. S /\ B e. S ) /\ ( K e. N /\ L e. N /\ Q e. R ) ) -> ( G gsum ( n e. N |-> ( n ( i e. N , j e. N |-> if ( i = K , if ( j = L , .0. , B ) , ( i A j ) ) ) ( Q ` n ) ) ) ) = ( G gsum ( n e. ( N \ { K } ) |-> ( n ( i e. ( N \ { K } ) , j e. ( N \ { L } ) |-> ( i A j ) ) ( Q ` n ) ) ) ) )

  proof
    cG
    ccmn
    wcel
    #
    cN
    cfn
    wcel
    #
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
    cG
    vn
    cN
    vn
    cv
    #
    @15
    cQ
    cfv
    #
    vi
    vj
    cN
    cN
    @3
    cK
    wceq
    #
    @4
    cL
    wceq
    #
    c.0
    cB
    cif
    #
    @5
    cif
    #
    cmpt2
    #
    co
    #
    cmpt
    #
    cgsu
    co
    cG
    vn
    cN
    cK
    csn
    #
    cdif
    #
    @24
    cun
    #
    @22
    cmpt
    #
    cgsu
    co
    cG
    vn
    @25
    @22
    cmpt
    #
    cgsu
    co
    #
    cK
    cK
    cQ
    cfv
    #
    @21
    co
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    vn
    @25
    @15
    @16
    vi
    vj
    @25
    cN
    cL
    csn
    cdif
    @5
    cmpt2
    co
    #
    cmpt
    #
    cgsu
    co
    #
    @14
    @23
    @27
    cG
    cgsu
    @14
    vn
    cN
    @26
    @22
    @13
    @2
    cN
    @26
    wceq
    #
    @9
    @10
    @11
    @37
    @12
    @10
    @26
    cN
    cN
    cK
    difsnid
    eqcomd
    3ad2ant1
    3ad2ant3
    mpteq1d
    oveq2d
    cA
    cB
    cP
    cQ
    cR
    cS
    vi
    vj
    vn
    cG
    cK
    cL
    cN
    c.0
    vr
    gsummatr01.p
    gsummatr01.r
    gsummatr01.0
    gsummatr01.s
    gsummatr01lem3
    @14
    @33
    @29
    c.0
    @32
    co
    #
    @29
    @36
    @14
    @31
    c.0
    @29
    @32
    @13
    @2
    @31
    c.0
    wceq
    @9
    @13
    vi
    vj
    cK
    @30
    cN
    cN
    @20
    c.0
    @21
    cvv
    @13
    @21
    eqidd
    @13
    @17
    @4
    @30
    wceq
    #
    wa
    #
    @20
    c.0
    wceq
    #
    @13
    @40
    @17
    @18
    wa
    #
    @41
    @12
    @10
    @40
    @42
    wb
    #
    @11
    @12
    cQ
    cP
    wcel
    #
    @30
    cL
    wceq
    #
    wa
    #
    @43
    cK
    vr
    cv
    #
    cfv
    #
    cL
    wceq
    @45
    vr
    cQ
    cP
    cR
    @47
    cQ
    wceq
    @48
    @30
    cL
    cK
    @47
    cQ
    fveq1
    eqeq1d
    gsummatr01.r
    elrab2
    @46
    @39
    @18
    @17
    @45
    @39
    @18
    wb
    @44
    @30
    cL
    @4
    eqeq2
    adantl
    anbi2d
    sylbi
    3ad2ant3
    @17
    @18
    @20
    @19
    c.0
    @17
    @19
    @5
    iftrue
    @18
    c.0
    cB
    iftrue
    sylan9eq
    syl6bi
    imp
    @10
    @11
    @12
    simp1
    @10
    @12
    @30
    cN
    wcel
    #
    @11
    @12
    @10
    @49
    cP
    cQ
    cR
    cK
    cL
    cN
    cK
    vr
    gsummatr01.p
    gsummatr01.r
    gsummatr01lem1
    ancoms
    3adant2
    c.0
    cvv
    wcel
    @13
    c.0
    cG
    c0g
    cfv
    cvv
    gsummatr01.0
    cG
    c0g
    fvex
    eqeltri
    a1i
    ovmpt2d
    3ad2ant3
    oveq2d
    @14
    cG
    cmnd
    wcel
    #
    @29
    cG
    cbs
    cfv
    #
    wcel
    @38
    @29
    wceq
    @2
    @9
    @50
    @13
    @0
    @50
    @1
    cG
    cmnmnd
    adantr
    3ad2ant1
    @14
    @51
    vn
    cG
    @25
    @22
    @51
    eqid
    #
    @0
    @1
    @9
    @13
    simp1l
    @2
    @9
    @25
    cfn
    wcel
    #
    @13
    @1
    @53
    @0
    cN
    @24
    diffi
    adantl
    3ad2ant1
    @14
    @22
    @51
    wcel
    vn
    @25
    @14
    @15
    @25
    wcel
    #
    wa
    @22
    @15
    @16
    cA
    co
    #
    @51
    @13
    @2
    @54
    @22
    @55
    wceq
    @9
    @13
    @54
    wa
    #
    vi
    vj
    @15
    @16
    cN
    cN
    @20
    @55
    @21
    cvv
    @56
    @21
    eqidd
    vi
    vn
    weq
    #
    @4
    @16
    wceq
    #
    wa
    #
    @56
    @20
    @15
    cK
    wceq
    #
    @16
    cL
    wceq
    #
    c.0
    cB
    cif
    #
    @55
    cif
    #
    @55
    @59
    @17
    @60
    @19
    @5
    @62
    @55
    @57
    @17
    @60
    wb
    @58
    @3
    @15
    cK
    eqeq1
    adantr
    @58
    @19
    @62
    wceq
    @57
    @58
    @18
    @61
    c.0
    cB
    @4
    @16
    cL
    eqeq1
    ifbid
    adantl
    @3
    @15
    @4
    @16
    cA
    oveq12
    ifbieq12d
    @54
    @63
    @55
    wceq
    @13
    @54
    @60
    @62
    @55
    @54
    @15
    cK
    @15
    cN
    cK
    eldifsni
    neneqd
    iffalsed
    adantl
    sylan9eqr
    @54
    @15
    cN
    wcel
    #
    @13
    @15
    cN
    @24
    eldifi
    #
    adantl
    @13
    @12
    @64
    @16
    cN
    wcel
    @54
    @10
    @11
    @12
    simp3
    #
    @65
    cP
    cQ
    cR
    cK
    cL
    cN
    @15
    vr
    gsummatr01.p
    gsummatr01.r
    gsummatr01lem1
    syl2an
    @56
    @15
    @16
    cA
    ovexd
    ovmpt2d
    3ad2antl3
    @14
    @54
    @55
    @51
    wcel
    #
    @9
    @13
    @54
    @67
    wi
    #
    @2
    @9
    @13
    @68
    @7
    @13
    @68
    wi
    @8
    @54
    @13
    @7
    @67
    @54
    @13
    @7
    @67
    wi
    #
    @13
    @12
    @64
    @69
    @54
    @66
    @65
    @7
    @5
    @51
    wcel
    #
    vj
    cN
    wral
    vi
    cN
    wral
    @12
    @64
    wa
    @67
    @6
    @70
    vi
    vj
    cN
    cN
    cS
    @51
    @5
    gsummatr01.s
    eleq2i
    2ralbii
    cA
    cP
    cQ
    cR
    vi
    vj
    cG
    cK
    cL
    cN
    @15
    vr
    gsummatr01.p
    gsummatr01.r
    gsummatr01lem2
    syl5bi
    syl2anr
    ex
    com13
    adantr
    imp
    3adant1
    imp
    eqeltrd
    ralrimiva
    gsummptcl
    @51
    @32
    cG
    @29
    c.0
    @52
    @32
    eqid
    gsummatr01.0
    mndrid
    syl2anc
    @14
    @28
    @35
    cG
    cgsu
    @14
    vn
    @25
    @22
    @34
    cA
    cB
    cP
    cQ
    cR
    cS
    vi
    vj
    vn
    cG
    cK
    cL
    cN
    c.0
    vr
    gsummatr01.p
    gsummatr01.r
    gsummatr01.0
    gsummatr01.s
    gsummatr01lem4
    mpteq2dva
    oveq2d
    3eqtrd
    3eqtrd
end
