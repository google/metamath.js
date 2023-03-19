include "cn0.mm"
include "wcel.mm"
include "cv.mm"
include "clsw.mm"
include "cfv.mm"
include "wa.mm"
include "cpr.mm"
include "cword.mm"
include "chash.mm"
include "c2.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cc0.mm"
include "c1.mm"
include "cop.mm"
include "csubstr.mm"
include "w3a.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "oveq1.mm"
include "preq2d.mm"
include "eleq1d.mm"
include "3anbi123d.mm"
include "elrab2.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "simpll.mm"
include "clt.mm"
include "wbr.mm"
include "nn0re.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nn0ge0.mm"
include "2pos.mm"
include "addgegt0d.mm"
include "ad2antlr.mm"
include "wb.mm"
include "breq2.mm"
include "adantl.mm"
include "mpbird.mm"
include "hashgt0n0.mm"
include "syl2anc.mm"
include "jca.mm"
include "expcom.mm"
include "3ad2ant1.mm"
include "expd.mm"
include "impcom.mm"
include "lswcl.mm"
include "syl.mm"
include "simprr3.mm"
include "sylan2b.mm"
include "preq2.mm"
include "sylibr.mm"
include "fmptd.mm"

theorem wwlksnextfun
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cR: class R
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cN: class N
  let cV: class V
  let cW: class W
  let vi: setvar i
  assume wwlksnextbij0.v: |- V = ( Vtx ` G )
  assume wwlksnextbij0.e: |- E = ( Edg ` G )
  assume wwlksnextbij0.d: |- D = { w e. Word V | ( ( # ` w ) = ( N + 2 ) /\ ( w substr <. 0 , ( N + 1 ) >. ) = W /\ { ( lastS ` W ) , ( lastS ` w ) } e. E ) }
  assume wwlksnextbij.r: |- R = { n e. V | { ( lastS ` W ) , n } e. E }
  assume wwlksnextbij.f: |- F = ( t e. D |-> ( lastS ` t ) )

  disjoint G w
  disjoint N w
  disjoint W w
  disjoint D t
  disjoint E n
  disjoint E w
  disjoint N t
  disjoint t w
  disjoint R t
  disjoint V n
  disjoint V w
  disjoint W n
  disjoint n t
  disjoint G i
  disjoint i w
  disjoint N i
  assert |- ( N e. NN0 -> F : D --> R )

  proof
    cN
    cn0
    wcel
    #
    vt
    cD
    vt
    cv
    #
    clsw
    cfv
    #
    cR
    cF
    @0
    @1
    cD
    wcel
    #
    wa
    @2
    cV
    wcel
    #
    cW
    clsw
    cfv
    #
    @2
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @2
    cR
    wcel
    @3
    @0
    @1
    cV
    cword
    #
    wcel
    #
    @1
    chash
    cfv
    #
    cN
    c2
    caddc
    co
    #
    wceq
    #
    @1
    cc0
    cN
    c1
    caddc
    co
    cop
    #
    csubstr
    co
    #
    cW
    wceq
    #
    @7
    w3a
    #
    wa
    #
    @8
    vw
    cv
    #
    chash
    cfv
    #
    @12
    wceq
    #
    @19
    @14
    csubstr
    co
    #
    cW
    wceq
    #
    @5
    @19
    clsw
    cfv
    #
    cpr
    #
    cE
    wcel
    #
    w3a
    @17
    vw
    @1
    @9
    cD
    @19
    @1
    wceq
    #
    @21
    @13
    @23
    @16
    @26
    @7
    @27
    @20
    @11
    @12
    @19
    @1
    chash
    fveq2
    eqeq1d
    @27
    @22
    @15
    cW
    @19
    @1
    @14
    csubstr
    oveq1
    eqeq1d
    @27
    @25
    @6
    cE
    @27
    @24
    @2
    @5
    @19
    @1
    clsw
    fveq2
    preq2d
    eleq1d
    3anbi123d
    wwlksnextbij0.d
    elrab2
    @0
    @18
    wa
    #
    @4
    @7
    @28
    @10
    @1
    c0
    wne
    #
    wa
    #
    @4
    @18
    @0
    @30
    @17
    @10
    @0
    @30
    wi
    @17
    @10
    @0
    @30
    @13
    @16
    @10
    @0
    wa
    #
    @30
    wi
    @7
    @31
    @13
    @30
    @31
    @13
    wa
    #
    @10
    @29
    @10
    @0
    @13
    simpll
    #
    @32
    @10
    cc0
    @11
    clt
    wbr
    #
    @29
    @33
    @32
    @34
    cc0
    @12
    clt
    wbr
    #
    @0
    @35
    @10
    @13
    @0
    cN
    c2
    cN
    nn0re
    c2
    cr
    wcel
    @0
    2re
    a1i
    cN
    nn0ge0
    cc0
    c2
    clt
    wbr
    @0
    2pos
    a1i
    addgegt0d
    ad2antlr
    @13
    @34
    @35
    wb
    @31
    @11
    @12
    cc0
    clt
    breq2
    adantl
    mpbird
    @1
    @9
    hashgt0n0
    syl2anc
    jca
    expcom
    3ad2ant1
    expd
    impcom
    impcom
    cV
    @1
    lswcl
    syl
    @13
    @16
    @7
    @10
    @0
    simprr3
    jca
    sylan2b
    @5
    vn
    cv
    #
    cpr
    #
    cE
    wcel
    @7
    vn
    @2
    cV
    cR
    @36
    @2
    wceq
    @37
    @6
    cE
    @36
    @2
    @5
    preq2
    eleq1d
    wwlksnextbij.r
    elrab2
    sylibr
    wwlksnextbij.f
    fmptd
end
