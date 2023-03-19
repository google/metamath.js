include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "ltrnset.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isltrn
  let cA: class A
  let cB: class B
  let cD: class D
  let cT: class T
  let cF: class F
  let cH: class H
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cW: class W
  let vq: setvar q
  let vp: setvar p
  let vk: setvar k
  let vf: setvar f
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
  disjoint K p
  disjoint K q
  disjoint W p
  disjoint W q
  disjoint F p
  disjoint F q
  disjoint k p
  disjoint k q
  disjoint A k
  disjoint f k
  disjoint D f
  disjoint D k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint .\/ k
  disjoint f p
  disjoint f q
  disjoint f w
  disjoint K f
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
  disjoint W f
  disjoint W w
  disjoint A f
  disjoint F f
  disjoint .\/ f
  disjoint .<_ f
  disjoint ./\ f
  assert |- ( ( K e. B /\ W e. H ) -> ( F e. T <-> ( F e. D /\ A. p e. A A. q e. A ( ( -. p .<_ W /\ -. q .<_ W ) -> ( ( p .\/ ( F ` p ) ) ./\ W ) = ( ( q .\/ ( F ` q ) ) ./\ W ) ) ) ) )

  proof
    cK
    cB
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cT
    wcel
    cF
    vp
    cv
    #
    cW
    c.le
    wbr
    wn
    vq
    cv
    #
    cW
    c.le
    wbr
    wn
    wa
    #
    @1
    @1
    vf
    cv
    #
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    @2
    @2
    @4
    cfv
    #
    c.or
    co
    #
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
    wcel
    cF
    cD
    wcel
    @3
    @1
    @1
    cF
    cfv
    #
    c.or
    co
    #
    cW
    c.an
    co
    #
    @2
    @2
    cF
    cfv
    #
    c.or
    co
    #
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
    wa
    @0
    cT
    @14
    cF
    cA
    cB
    cD
    cT
    vf
    cH
    c.or
    cK
    c.le
    c.an
    cW
    vq
    vp
    ltrnset.l
    ltrnset.j
    ltrnset.m
    ltrnset.a
    ltrnset.h
    ltrnset.d
    ltrnset.t
    ltrnset
    eleq2d
    @13
    @23
    vf
    cF
    cD
    @4
    cF
    wceq
    #
    @12
    @22
    vp
    vq
    cA
    cA
    @24
    @11
    @21
    @3
    @24
    @7
    @17
    @10
    @20
    @24
    @6
    @16
    cW
    c.an
    @24
    @5
    @15
    @1
    c.or
    @1
    @4
    cF
    fveq1
    oveq2d
    oveq1d
    @24
    @9
    @19
    cW
    c.an
    @24
    @8
    @18
    @2
    c.or
    @2
    @4
    cF
    fveq1
    oveq2d
    oveq1d
    eqeq12d
    imbi2d
    2ralbidv
    elrab
    syl6bb
end
