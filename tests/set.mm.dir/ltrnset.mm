include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cldil.mm"
include "crab.mm"
include "cmpt.mm"
include "cltrn.mm"
include "ltrnfset.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "breq2.mm"
include "notbid.mm"
include "anbi12d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "2ralbidv.mm"
include "rabeqbidv.mm"
include "eqid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem ltrnset
  let cA: class A
  let cB: class B
  let cD: class D
  let cT: class T
  let vf: setvar f
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vw: setvar w
  assume ltrnset.l: |- .<_ = ( le ` K )
  assume ltrnset.j: |- .\/ = ( join ` K )
  assume ltrnset.m: |- ./\ = ( meet ` K )
  assume ltrnset.a: |- A = ( Atoms ` K )
  assume ltrnset.h: |- H = ( LHyp ` K )
  assume ltrnset.d: |- D = ( ( LDil ` K ) ` W )
  assume ltrnset.t: |- T = ( ( LTrn ` K ) ` W )

  disjoint p q
  disjoint A p
  disjoint A q
  disjoint D f
  disjoint f p
  disjoint f q
  disjoint K f
  disjoint K p
  disjoint K q
  disjoint W f
  disjoint W p
  disjoint W q
  disjoint k p
  disjoint k q
  disjoint A k
  disjoint f k
  disjoint D k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint .\/ k
  disjoint f w
  disjoint K k
  disjoint p w
  disjoint q w
  disjoint K w
  disjoint .<_ k
  disjoint ./\ k
  disjoint A w
  disjoint D w
  disjoint .\/ w
  disjoint .<_ w
  disjoint ./\ w
  disjoint W w
  assert |- ( ( K e. B /\ W e. H ) -> T = { f e. D | A. p e. A A. q e. A ( ( -. p .<_ W /\ -. q .<_ W ) -> ( ( p .\/ ( f ` p ) ) ./\ W ) = ( ( q .\/ ( f ` q ) ) ./\ W ) ) } )

  proof
    cK
    cB
    wcel
    #
    cW
    cH
    wcel
    cT
    cW
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
    @2
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @1
    @1
    vf
    cv
    #
    cfv
    c.or
    co
    #
    @2
    c.an
    co
    #
    @5
    @5
    @9
    cfv
    c.or
    co
    #
    @2
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
    vp
    cA
    wral
    #
    vf
    @2
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
    cfv
    #
    @1
    cW
    c.le
    wbr
    #
    wn
    #
    @5
    cW
    c.le
    wbr
    #
    wn
    #
    wa
    #
    @10
    cW
    c.an
    co
    #
    @12
    cW
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
    vp
    cA
    wral
    #
    vf
    cD
    crab
    #
    @0
    cT
    cW
    cK
    cltrn
    cfv
    #
    cfv
    @21
    ltrnset.t
    @0
    cW
    @33
    @20
    vw
    cA
    cB
    vf
    cH
    c.or
    cK
    c.le
    c.an
    vq
    vp
    ltrnset.l
    ltrnset.j
    ltrnset.m
    ltrnset.a
    ltrnset.h
    ltrnfset
    fveq1d
    syl5eq
    vw
    cW
    @19
    @32
    cH
    @20
    @2
    cW
    wceq
    #
    @16
    @31
    vf
    @18
    cD
    @34
    @18
    cW
    @17
    cfv
    #
    cD
    @2
    cW
    @17
    fveq2
    ltrnset.d
    syl6eqr
    @34
    @15
    @30
    vp
    vq
    cA
    cA
    @34
    @8
    @26
    @14
    @29
    @34
    @4
    @23
    @7
    @25
    @34
    @3
    @22
    @2
    cW
    @1
    c.le
    breq2
    notbid
    @34
    @6
    @24
    @2
    cW
    @5
    c.le
    breq2
    notbid
    anbi12d
    @34
    @11
    @27
    @13
    @28
    @2
    cW
    @10
    c.an
    oveq2
    @2
    cW
    @12
    c.an
    oveq2
    eqeq12d
    imbi12d
    2ralbidv
    rabeqbidv
    @20
    eqid
    @31
    vf
    cD
    cD
    @35
    cvv
    ltrnset.d
    cW
    @17
    fvex
    eqeltri
    rabex
    fvmpt
    sylan9eq
end
