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
include "cbs.mm"
include "cfv.mm"
include "cplusg.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "eqid.mm"
include "simpl.mm"
include "3ad2ant1.mm"
include "diffi.mm"
include "adantl.mm"
include "cvv.mm"
include "eqidd.mm"
include "weq.mm"
include "wb.mm"
include "eqeq1.mm"
include "adantr.mm"
include "ifbid.mm"
include "oveq12.mm"
include "ifbieq12d.mm"
include "eldifsni.mm"
include "neneqd.mm"
include "iffalsed.mm"
include "sylan9eqr.mm"
include "eldifi.mm"
include "wi.mm"
include "gsummatr01lem1.mm"
include "expcom.mm"
include "syl11.mm"
include "3ad2ant3.mm"
include "imp.mm"
include "ovexd.mm"
include "ovmpt2d.mm"
include "3ad2antl3.mm"
include "eleq2i.mm"
include "2ralbii.mm"
include "gsummatr01lem2.mm"
include "sylan2.mm"
include "ex.mm"
include "com3r.mm"
include "sylbi.mm"
include "imp31.mm"
include "3adantl1.mm"
include "eqeltrd.mm"
include "simp31.mm"
include "neldifsnd.mm"
include "iftrue.mm"
include "sylan9eq.mm"
include "simpr1.mm"
include "ancoms.mm"
include "3adant2.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ifexg.mm"
include "sylancr.mm"
include "adantll.mm"
include "3adant1.mm"
include "cmnd.mm"
include "cmnmnd.mm"
include "mndidcl.mm"
include "syl.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "ifcld.mm"
include "id.mm"
include "fveq2.mm"
include "oveq12d.mm"
include "gsumunsn.mm"

theorem gsummatr01lem3
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
  assert |- ( ( ( G e. CMnd /\ N e. Fin ) /\ ( A. i e. N A. j e. N ( i A j ) e. S /\ B e. S ) /\ ( K e. N /\ L e. N /\ Q e. R ) ) -> ( G gsum ( n e. ( ( N \ { K } ) u. { K } ) |-> ( n ( i e. N , j e. N |-> if ( i = K , if ( j = L , .0. , B ) , ( i A j ) ) ) ( Q ` n ) ) ) ) = ( ( G gsum ( n e. ( N \ { K } ) |-> ( n ( i e. N , j e. N |-> if ( i = K , if ( j = L , .0. , B ) , ( i A j ) ) ) ( Q ` n ) ) ) ) ( +g ` G ) ( K ( i e. N , j e. N |-> if ( i = K , if ( j = L , .0. , B ) , ( i A j ) ) ) ( Q ` K ) ) ) )

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
    cN
    cK
    csn
    #
    cdif
    #
    cG
    cbs
    cfv
    #
    cG
    cplusg
    cfv
    #
    vn
    cG
    cK
    cN
    vn
    cv
    #
    @19
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
    cK
    cK
    cQ
    cfv
    #
    @25
    co
    #
    @17
    eqid
    #
    @18
    eqid
    @2
    @9
    @0
    @13
    @0
    @1
    simpl
    3ad2ant1
    @2
    @9
    @16
    cfn
    wcel
    #
    @13
    @1
    @30
    @0
    cN
    @15
    diffi
    adantl
    3ad2ant1
    @14
    @19
    @16
    wcel
    #
    wa
    @26
    @19
    @20
    cA
    co
    #
    @17
    @13
    @2
    @31
    @26
    @32
    wceq
    @9
    @13
    @31
    wa
    #
    vi
    vj
    @19
    @20
    cN
    cN
    @24
    @32
    @25
    cvv
    @33
    @25
    eqidd
    vi
    vn
    weq
    #
    @4
    @20
    wceq
    #
    wa
    #
    @33
    @24
    @19
    cK
    wceq
    #
    @20
    cL
    wceq
    #
    c.0
    cB
    cif
    #
    @32
    cif
    #
    @32
    @36
    @21
    @37
    @23
    @5
    @39
    @32
    @34
    @21
    @37
    wb
    @35
    @3
    @19
    cK
    eqeq1
    adantr
    @35
    @23
    @39
    wceq
    @34
    @35
    @22
    @38
    c.0
    cB
    @4
    @20
    cL
    eqeq1
    ifbid
    adantl
    @3
    @19
    @4
    @20
    cA
    oveq12
    ifbieq12d
    @31
    @40
    @32
    wceq
    @13
    @31
    @37
    @39
    @32
    @31
    @19
    cK
    @19
    cN
    cK
    eldifsni
    neneqd
    iffalsed
    adantl
    sylan9eqr
    @31
    @19
    cN
    wcel
    #
    @13
    @19
    cN
    @15
    eldifi
    #
    adantl
    @13
    @31
    @20
    cN
    wcel
    #
    @12
    @10
    @31
    @43
    wi
    @11
    @41
    @12
    @43
    @31
    @12
    @41
    @43
    cP
    cQ
    cR
    cK
    cL
    cN
    @19
    vr
    gsummatr01.p
    gsummatr01.r
    gsummatr01lem1
    expcom
    @42
    syl11
    3ad2ant3
    imp
    @33
    @19
    @20
    cA
    ovexd
    ovmpt2d
    3ad2antl3
    @9
    @13
    @31
    @32
    @17
    wcel
    #
    @2
    @9
    @13
    @31
    @44
    @7
    @13
    @31
    @44
    wi
    wi
    #
    @8
    @7
    @5
    @17
    wcel
    #
    vj
    cN
    wral
    vi
    cN
    wral
    #
    @45
    @6
    @46
    vi
    vj
    cN
    cN
    cS
    @17
    @5
    gsummatr01.s
    eleq2i
    2ralbii
    @13
    @31
    @47
    @44
    @12
    @10
    @31
    @47
    @44
    wi
    #
    wi
    @11
    @12
    @31
    @48
    @31
    @12
    @41
    @48
    @42
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
    @19
    vr
    gsummatr01.p
    gsummatr01.r
    gsummatr01lem2
    sylan2
    ex
    3ad2ant3
    com3r
    sylbi
    adantr
    imp31
    3adantl1
    eqeltrd
    @2
    @9
    @10
    @11
    @12
    simp31
    @14
    cK
    cN
    neldifsnd
    @14
    @28
    @27
    cL
    wceq
    #
    c.0
    cB
    cif
    #
    @17
    @9
    @13
    @28
    @50
    wceq
    #
    @2
    @8
    @13
    @51
    @7
    @8
    @13
    wa
    #
    vi
    vj
    cK
    @27
    cN
    cN
    @24
    @50
    @25
    cvv
    @52
    @25
    eqidd
    @21
    @4
    @27
    wceq
    #
    wa
    @24
    @50
    wceq
    @52
    @21
    @53
    @24
    @23
    @50
    @21
    @23
    @5
    iftrue
    @53
    @22
    @49
    c.0
    cB
    @4
    @27
    cL
    eqeq1
    ifbid
    sylan9eq
    adantl
    @8
    @10
    @11
    @12
    simpr1
    @13
    @27
    cN
    wcel
    #
    @8
    @10
    @12
    @54
    @11
    @12
    @10
    @54
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
    adantl
    @52
    c.0
    cvv
    wcel
    @8
    @50
    cvv
    wcel
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
    @8
    @13
    simpl
    @49
    c.0
    cB
    cvv
    cS
    ifexg
    sylancr
    ovmpt2d
    adantll
    3adant1
    @14
    @49
    c.0
    cB
    @17
    @2
    @9
    c.0
    @17
    wcel
    #
    @13
    @0
    @55
    @1
    @0
    cG
    cmnd
    wcel
    @55
    cG
    cmnmnd
    @17
    cG
    c.0
    @29
    gsummatr01.0
    mndidcl
    syl
    adantr
    3ad2ant1
    @9
    @2
    cB
    @17
    wcel
    #
    @13
    @8
    @56
    @7
    @8
    @56
    cS
    @17
    cB
    gsummatr01.s
    eleq2i
    biimpi
    adantl
    3ad2ant2
    ifcld
    eqeltrd
    @37
    @19
    cK
    @20
    @27
    @25
    @37
    id
    @19
    cK
    cQ
    fveq2
    oveq12d
    gsumunsn
end
