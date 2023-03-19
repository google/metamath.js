include "com.mm"
include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "cpw.mm"
include "ccrd.mm"
include "csuc.mm"
include "ackbij1lem8.mm"
include "cv.mm"
include "wceq.mm"
include "c0.mm"
include "pweq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "suceq.mm"
include "syl.mm"
include "eqeq12d.mm"
include "weq.mm"
include "c1o.mm"
include "df-1o.mm"
include "pw0.mm"
include "fveq2i.mm"
include "cvv.mm"
include "0ex.mm"
include "cardsn.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "ackbij1lem13.mm"
include "3eqtr4i.mm"
include "wa.mm"
include "coa.mm"
include "co.mm"
include "oveq2.mm"
include "adantl.mm"
include "ackbij1lem5.mm"
include "adantr.mm"
include "cun.mm"
include "df-suc.mm"
include "equncomi.mm"
include "cfn.mm"
include "cin.mm"
include "ackbij1lem4.mm"
include "ackbij1lem3.mm"
include "incom.mm"
include "word.mm"
include "nnord.mm"
include "orddisj.mm"
include "syl5eq.mm"
include "ackbij1lem9.mm"
include "syl3anc.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "nnfi.mm"
include "pwfi.mm"
include "sylib.mm"
include "ficardom.mm"
include "ackbij1lem10.mm"
include "ffvelrni.mm"
include "nnasuc.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"
include "ex.mm"
include "finds.mm"

theorem ackbij1lem14
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cG: class G
  let cH: class H
  let cB: class B
  assume ackbij.f: |- F = ( x e. ( ~P _om i^i Fin ) |-> ( card ` U_ y e. x ( { y } X. ~P y ) ) )

  disjoint F x
  disjoint F y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint G a
  disjoint G b
  disjoint G c
  disjoint G x
  disjoint G y
  disjoint H a
  disjoint H b
  disjoint H c
  disjoint H x
  disjoint H y
  disjoint A a
  disjoint A b
  disjoint A c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B x
  disjoint B y
  assert |- ( A e. _om -> ( F ` { A } ) = suc ( F ` A ) )

  proof
    cA
    com
    wcel
    cA
    csn
    cF
    cfv
    cA
    cpw
    #
    ccrd
    cfv
    #
    cA
    cF
    cfv
    #
    csuc
    #
    vx
    vy
    cA
    cF
    ackbij.f
    ackbij1lem8
    va
    cv
    #
    cpw
    #
    ccrd
    cfv
    #
    @4
    cF
    cfv
    #
    csuc
    #
    wceq
    c0
    cpw
    #
    ccrd
    cfv
    #
    c0
    cF
    cfv
    #
    csuc
    #
    wceq
    vb
    cv
    #
    cpw
    #
    ccrd
    cfv
    #
    @13
    cF
    cfv
    #
    csuc
    #
    wceq
    #
    @13
    csuc
    #
    cpw
    #
    ccrd
    cfv
    #
    @19
    cF
    cfv
    #
    csuc
    #
    wceq
    #
    @1
    @3
    wceq
    va
    vb
    cA
    @4
    c0
    wceq
    #
    @6
    @10
    @8
    @12
    @25
    @5
    @9
    ccrd
    @4
    c0
    pweq
    fveq2d
    @25
    @7
    @11
    wceq
    @8
    @12
    wceq
    @4
    c0
    cF
    fveq2
    @7
    @11
    suceq
    syl
    eqeq12d
    va
    vb
    weq
    #
    @6
    @15
    @8
    @17
    @26
    @5
    @14
    ccrd
    @4
    @13
    pweq
    fveq2d
    @26
    @7
    @16
    wceq
    @8
    @17
    wceq
    @4
    @13
    cF
    fveq2
    @7
    @16
    suceq
    syl
    eqeq12d
    @4
    @19
    wceq
    #
    @6
    @21
    @8
    @23
    @27
    @5
    @20
    ccrd
    @4
    @19
    pweq
    fveq2d
    @27
    @7
    @22
    wceq
    @8
    @23
    wceq
    @4
    @19
    cF
    fveq2
    @7
    @22
    suceq
    syl
    eqeq12d
    @4
    cA
    wceq
    #
    @6
    @1
    @8
    @3
    @28
    @5
    @0
    ccrd
    @4
    cA
    pweq
    fveq2d
    @28
    @7
    @2
    wceq
    @8
    @3
    wceq
    @4
    cA
    cF
    fveq2
    @7
    @2
    suceq
    syl
    eqeq12d
    c1o
    c0
    csuc
    #
    @10
    @12
    df-1o
    @10
    c0
    csn
    #
    ccrd
    cfv
    #
    c1o
    @9
    @30
    ccrd
    pw0
    fveq2i
    c0
    cvv
    wcel
    @31
    c1o
    wceq
    0ex
    c0
    cvv
    cardsn
    ax-mp
    eqtri
    @11
    c0
    wceq
    @12
    @29
    wceq
    vx
    vy
    cF
    ackbij.f
    ackbij1lem13
    @11
    c0
    suceq
    ax-mp
    3eqtr4i
    @13
    com
    wcel
    #
    @18
    @24
    @32
    @18
    wa
    #
    @15
    @15
    coa
    co
    #
    @15
    @17
    coa
    co
    #
    @21
    @23
    @18
    @34
    @35
    wceq
    @32
    @15
    @17
    @15
    coa
    oveq2
    adantl
    @32
    @21
    @34
    wceq
    @18
    @13
    ackbij1lem5
    adantr
    @33
    @23
    @15
    @16
    coa
    co
    #
    csuc
    #
    @35
    @33
    @22
    @36
    wceq
    @23
    @37
    wceq
    @33
    @22
    @13
    csn
    #
    @13
    cun
    #
    cF
    cfv
    #
    @36
    @19
    @39
    cF
    @19
    @13
    @38
    @13
    df-suc
    equncomi
    fveq2i
    @33
    @40
    @38
    cF
    cfv
    #
    @16
    coa
    co
    #
    @36
    @33
    @38
    com
    cpw
    cfn
    cin
    #
    wcel
    #
    @13
    @43
    wcel
    #
    @38
    @13
    cin
    #
    c0
    wceq
    #
    @40
    @42
    wceq
    @32
    @44
    @18
    @13
    ackbij1lem4
    adantr
    @32
    @45
    @18
    @13
    ackbij1lem3
    adantr
    #
    @32
    @47
    @18
    @32
    @46
    @13
    @38
    cin
    #
    c0
    @38
    @13
    incom
    @32
    @13
    word
    @49
    c0
    wceq
    @13
    nnord
    @13
    orddisj
    syl
    syl5eq
    adantr
    vx
    vy
    @38
    @13
    cF
    ackbij.f
    ackbij1lem9
    syl3anc
    @33
    @41
    @15
    @16
    coa
    @32
    @41
    @15
    wceq
    @18
    vx
    vy
    @13
    cF
    ackbij.f
    ackbij1lem8
    adantr
    oveq1d
    eqtrd
    syl5eq
    @22
    @36
    suceq
    syl
    @33
    @15
    com
    wcel
    #
    @16
    com
    wcel
    #
    @35
    @37
    wceq
    @33
    @14
    cfn
    wcel
    #
    @50
    @32
    @52
    @18
    @32
    @13
    cfn
    wcel
    @52
    @13
    nnfi
    @13
    pwfi
    sylib
    adantr
    @14
    ficardom
    syl
    @33
    @45
    @51
    @48
    @43
    com
    @13
    cF
    vx
    vy
    cF
    ackbij.f
    ackbij1lem10
    ffvelrni
    syl
    @15
    @16
    nnasuc
    syl2anc
    eqtr4d
    3eqtr4d
    ex
    finds
    eqtrd
end
