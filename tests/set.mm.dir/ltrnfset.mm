include "wcel.mm"
include "cvv.mm"
include "cltrn.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cldil.mm"
include "crab.mm"
include "cmpt.mm"
include "elex.mm"
include "clh.mm"
include "cple.mm"
include "cjn.mm"
include "cmee.mm"
include "catm.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "breqd.mm"
include "notbid.mm"
include "anbi12d.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "df-ltrn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl.mm"

theorem ltrnfset
  let vw: setvar w
  let cA: class A
  let cC: class C
  let vf: setvar f
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let cD: class D
  assume ltrnset.l: |- .<_ = ( le ` K )
  assume ltrnset.j: |- .\/ = ( join ` K )
  assume ltrnset.m: |- ./\ = ( meet ` K )
  assume ltrnset.a: |- A = ( Atoms ` K )
  assume ltrnset.h: |- H = ( LHyp ` K )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint H w
  disjoint f p
  disjoint f q
  disjoint f w
  disjoint K f
  disjoint p w
  disjoint K p
  disjoint q w
  disjoint K q
  disjoint K w
  disjoint k p
  disjoint k q
  disjoint A k
  disjoint f k
  disjoint D f
  disjoint D k
  disjoint k w
  disjoint H k
  disjoint .\/ k
  disjoint K k
  disjoint .<_ k
  disjoint ./\ k
  assert |- ( K e. C -> ( LTrn ` K ) = ( w e. H |-> { f e. ( ( LDil ` K ) ` w ) | A. p e. A A. q e. A ( ( -. p .<_ w /\ -. q .<_ w ) -> ( ( p .\/ ( f ` p ) ) ./\ w ) = ( ( q .\/ ( f ` q ) ) ./\ w ) ) } ) )

  proof
    cK
    cC
    wcel
    cK
    cvv
    wcel
    cK
    cltrn
    cfv
    vw
    cH
    vp
    cv
    #
    vw
    cv
    #
    c.le
    wbr
    #
    wn
    #
    vq
    cv
    #
    @1
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @0
    @0
    vf
    cv
    #
    cfv
    #
    c.or
    co
    #
    @1
    c.an
    co
    #
    @4
    @4
    @8
    cfv
    #
    c.or
    co
    #
    @1
    c.an
    co
    #
    wceq
    #
    wi
    #
    vq
    cA
    wral
    #
    vp
    cA
    wral
    #
    vf
    @1
    cK
    cldil
    cfv
    #
    cfv
    #
    crab
    #
    cmpt
    #
    wceq
    cK
    cC
    elex
    vk
    cK
    vw
    vk
    cv
    #
    clh
    cfv
    #
    @0
    @1
    @23
    cple
    cfv
    #
    wbr
    #
    wn
    #
    @4
    @1
    @25
    wbr
    #
    wn
    #
    wa
    #
    @0
    @9
    @23
    cjn
    cfv
    #
    co
    #
    @1
    @23
    cmee
    cfv
    #
    co
    #
    @4
    @12
    @31
    co
    #
    @1
    @33
    co
    #
    wceq
    #
    wi
    #
    vq
    @23
    catm
    cfv
    #
    wral
    #
    vp
    @39
    wral
    #
    vf
    @1
    @23
    cldil
    cfv
    #
    cfv
    #
    crab
    #
    cmpt
    @22
    cvv
    cltrn
    @23
    cK
    wceq
    #
    vw
    @24
    @44
    cH
    @21
    @45
    @24
    cK
    clh
    cfv
    #
    cH
    @23
    cK
    clh
    fveq2
    ltrnset.h
    syl6eqr
    @45
    @41
    @18
    vf
    @43
    @20
    @45
    @1
    @42
    @19
    @23
    cK
    cldil
    fveq2
    fveq1d
    @45
    @40
    @17
    vp
    @39
    cA
    @45
    @39
    cK
    catm
    cfv
    cA
    @23
    cK
    catm
    fveq2
    ltrnset.a
    syl6eqr
    #
    @45
    @38
    @16
    vq
    @39
    cA
    @47
    @45
    @30
    @7
    @37
    @15
    @45
    @27
    @3
    @29
    @6
    @45
    @26
    @2
    @45
    @25
    c.le
    @0
    @1
    @45
    @25
    cK
    cple
    cfv
    c.le
    @23
    cK
    cple
    fveq2
    ltrnset.l
    syl6eqr
    #
    breqd
    notbid
    @45
    @28
    @5
    @45
    @25
    c.le
    @4
    @1
    @48
    breqd
    notbid
    anbi12d
    @45
    @34
    @11
    @36
    @14
    @45
    @32
    @10
    @1
    @1
    @33
    c.an
    @45
    @33
    cK
    cmee
    cfv
    c.an
    @23
    cK
    cmee
    fveq2
    ltrnset.m
    syl6eqr
    #
    @45
    @31
    c.or
    @0
    @9
    @45
    @31
    cK
    cjn
    cfv
    c.or
    @23
    cK
    cjn
    fveq2
    ltrnset.j
    syl6eqr
    #
    oveqd
    @45
    @1
    eqidd
    #
    oveq123d
    @45
    @35
    @13
    @1
    @1
    @33
    c.an
    @49
    @45
    @31
    c.or
    @4
    @12
    @50
    oveqd
    @51
    oveq123d
    eqeq12d
    imbi12d
    raleqbidv
    raleqbidv
    rabeqbidv
    mpteq12dv
    vw
    vf
    vk
    vq
    vp
    df-ltrn
    vw
    cH
    @21
    cH
    @46
    cvv
    ltrnset.h
    cK
    clh
    fvex
    eqeltri
    mptex
    fvmpt
    syl
end
