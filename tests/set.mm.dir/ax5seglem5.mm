include "cn.mm"
include "wcel.mm"
include "cee.mm"
include "cfv.mm"
include "w3a.mm"
include "wa.mm"
include "wne.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "cfz.mm"
include "wral.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "wi.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "eqeq2d.mm"
include "ralbidv.mm"
include "biimparc.mm"
include "wb.mm"
include "simplr1.mm"
include "simplr2.mm"
include "eqeefv.mm"
include "syl2anc.mm"
include "cc.mm"
include "fveecn.mm"
include "sylan.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "0re.mm"
include "1re.mm"
include "elicc2i.mm"
include "simp1bi.mm"
include "recnd.mm"
include "ad2antlr.mm"
include "ax-1cn.mm"
include "npcan.mm"
include "mpan.mm"
include "oveq1d.mm"
include "mulid2.mm"
include "sylan9eqr.mm"
include "subcl.mm"
include "adantl.mm"
include "simpr.mm"
include "simpl.mm"
include "adddird.mm"
include "eqtr3d.mm"
include "eqeq1d.mm"
include "eqcom.mm"
include "syl6bb.mm"
include "ralbidva.mm"
include "bitrd.mm"
include "syl5ibr.mm"
include "expd.mm"
include "impr.mm"
include "necon3d.mm"
include "ex.mm"
include "com23.mm"
include "exp4a.mm"
include "3imp2.mm"
include "simplr3.mm"
include "eqeelen.mm"
include "necon3bid.mm"
include "mpbid.mm"

theorem ax5seglem5
  let cA: class A
  let cB: class B
  let cC: class C
  let cT: class T
  let vi: setvar i
  let vj: setvar j
  let cN: class N

  disjoint A i
  disjoint A j
  disjoint i j
  disjoint B i
  disjoint B j
  disjoint C i
  disjoint C j
  disjoint T i
  disjoint N i
  disjoint N j
  assert |- ( ( ( N e. NN /\ ( A e. ( EE ` N ) /\ B e. ( EE ` N ) /\ C e. ( EE ` N ) ) ) /\ ( A =/= B /\ T e. ( 0 [,] 1 ) /\ A. i e. ( 1 ... N ) ( B ` i ) = ( ( ( 1 - T ) x. ( A ` i ) ) + ( T x. ( C ` i ) ) ) ) ) -> sum_ j e. ( 1 ... N ) ( ( ( A ` j ) - ( C ` j ) ) ^ 2 ) =/= 0 )

  proof
    cN
    cn
    wcel
    #
    cA
    cN
    cee
    cfv
    #
    wcel
    #
    cB
    @1
    wcel
    #
    cC
    @1
    wcel
    #
    w3a
    wa
    #
    cA
    cB
    wne
    #
    cT
    cc0
    c1
    cicc
    co
    wcel
    #
    vi
    cv
    #
    cB
    cfv
    #
    c1
    cT
    cmin
    co
    #
    @8
    cA
    cfv
    #
    cmul
    co
    #
    cT
    @8
    cC
    cfv
    #
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    c1
    cN
    cfz
    co
    #
    wral
    #
    w3a
    #
    wa
    #
    cA
    cC
    wne
    #
    @17
    vj
    cv
    #
    cA
    cfv
    @22
    cC
    cfv
    cmin
    co
    c2
    cexp
    co
    vj
    csu
    #
    cc0
    wne
    @5
    @6
    @7
    @18
    @21
    @5
    @6
    @7
    @18
    @21
    @5
    @7
    @18
    wa
    #
    @6
    @21
    @5
    @24
    @6
    @21
    wi
    @5
    @24
    wa
    cA
    cC
    cA
    cB
    @5
    @7
    @18
    cA
    cC
    wceq
    #
    cA
    cB
    wceq
    #
    wi
    @5
    @7
    wa
    #
    @18
    @25
    @26
    @18
    @25
    wa
    @26
    @27
    @9
    @12
    cT
    @11
    cmul
    co
    #
    caddc
    co
    #
    wceq
    #
    vi
    @17
    wral
    #
    @25
    @31
    @18
    @25
    @30
    @16
    vi
    @17
    @25
    @29
    @15
    @9
    @25
    @28
    @14
    @12
    caddc
    @25
    @11
    @13
    cT
    cmul
    @8
    cA
    cC
    fveq1
    oveq2d
    oveq2d
    eqeq2d
    ralbidv
    biimparc
    @27
    @26
    @11
    @9
    wceq
    #
    vi
    @17
    wral
    #
    @31
    @27
    @2
    @3
    @26
    @33
    wb
    @2
    @3
    @4
    @0
    @7
    simplr1
    #
    @2
    @3
    @4
    @0
    @7
    simplr2
    cA
    cB
    vi
    cN
    eqeefv
    syl2anc
    @27
    @32
    @30
    vi
    @17
    @27
    @8
    @17
    wcel
    #
    wa
    #
    @32
    @29
    @9
    wceq
    #
    @30
    @36
    @11
    cc
    wcel
    #
    cT
    cc
    wcel
    #
    @32
    @37
    wb
    @27
    @2
    @35
    @38
    @34
    cA
    @8
    cN
    fveecn
    sylan
    @7
    @39
    @5
    @35
    @7
    cT
    @7
    cT
    cr
    wcel
    cc0
    cT
    cle
    wbr
    cT
    c1
    cle
    wbr
    cc0
    c1
    cT
    0re
    1re
    elicc2i
    simp1bi
    recnd
    ad2antlr
    @38
    @39
    wa
    #
    @11
    @29
    @9
    @40
    @10
    cT
    caddc
    co
    #
    @11
    cmul
    co
    #
    @11
    @29
    @39
    @38
    @42
    c1
    @11
    cmul
    co
    @11
    @39
    @41
    c1
    @11
    cmul
    c1
    cc
    wcel
    #
    @39
    @41
    c1
    wceq
    ax-1cn
    c1
    cT
    npcan
    mpan
    oveq1d
    @11
    mulid2
    sylan9eqr
    @40
    @10
    cT
    @11
    @39
    @10
    cc
    wcel
    #
    @38
    @43
    @39
    @44
    ax-1cn
    c1
    cT
    subcl
    mpan
    adantl
    @38
    @39
    simpr
    @38
    @39
    simpl
    adddird
    eqtr3d
    eqeq1d
    syl2anc
    @29
    @9
    eqcom
    syl6bb
    ralbidva
    bitrd
    syl5ibr
    expd
    impr
    necon3d
    ex
    com23
    exp4a
    3imp2
    @20
    cA
    cC
    @23
    cc0
    @20
    @2
    @4
    @25
    @23
    cc0
    wceq
    wb
    @2
    @3
    @4
    @0
    @19
    simplr1
    @2
    @3
    @4
    @0
    @19
    simplr3
    cA
    cC
    vj
    cN
    eqeelen
    syl2anc
    necon3bid
    mpbid
end
