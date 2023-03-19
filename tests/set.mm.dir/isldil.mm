include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "ldilset.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isldil
  let vx: setvar x
  let cB: class B
  let cC: class C
  let cD: class D
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let c.le: class .<_
  let cW: class W
  let vk: setvar k
  let vw: setvar w
  let vf: setvar f
  assume ldilset.b: |- B = ( Base ` K )
  assume ldilset.l: |- .<_ = ( le ` K )
  assume ldilset.h: |- H = ( LHyp ` K )
  assume ldilset.i: |- I = ( LAut ` K )
  assume ldilset.d: |- D = ( ( LDil ` K ) ` W )

  disjoint B x
  disjoint K x
  disjoint W x
  disjoint F x
  disjoint k x
  disjoint B k
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint I f
  disjoint I k
  disjoint f w
  disjoint f x
  disjoint K f
  disjoint K k
  disjoint w x
  disjoint K w
  disjoint .<_ k
  disjoint B w
  disjoint I w
  disjoint .<_ w
  disjoint W f
  disjoint W w
  disjoint B f
  disjoint F f
  disjoint .<_ f
  assert |- ( ( K e. C /\ W e. H ) -> ( F e. D <-> ( F e. I /\ A. x e. B ( x .<_ W -> ( F ` x ) = x ) ) ) )

  proof
    cK
    cC
    wcel
    cW
    cH
    wcel
    wa
    #
    cF
    cD
    wcel
    cF
    vx
    cv
    #
    cW
    c.le
    wbr
    #
    @1
    vf
    cv
    #
    cfv
    #
    @1
    wceq
    #
    wi
    #
    vx
    cB
    wral
    #
    vf
    cI
    crab
    #
    wcel
    cF
    cI
    wcel
    @2
    @1
    cF
    cfv
    #
    @1
    wceq
    #
    wi
    #
    vx
    cB
    wral
    #
    wa
    @0
    cD
    @8
    cF
    vx
    cB
    cC
    cD
    vf
    cH
    cI
    cK
    c.le
    cW
    ldilset.b
    ldilset.l
    ldilset.h
    ldilset.i
    ldilset.d
    ldilset
    eleq2d
    @7
    @12
    vf
    cF
    cI
    @3
    cF
    wceq
    #
    @6
    @11
    vx
    cB
    @13
    @5
    @10
    @2
    @13
    @4
    @9
    @1
    @1
    @3
    cF
    fveq1
    eqeq1d
    imbi2d
    ralbidv
    elrab
    syl6bb
end
