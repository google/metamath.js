include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "dilsetN.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "eqeq1d.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem isdilN
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cF: class F
  let cK: class K
  let cL: class L
  let cM: class M
  let cW: class W
  let vd: setvar d
  let vk: setvar k
  let vf: setvar f
  assume dilset.a: |- A = ( Atoms ` K )
  assume dilset.s: |- S = ( PSubSp ` K )
  assume dilset.w: |- W = ( WAtoms ` K )
  assume dilset.m: |- M = ( PAut ` K )
  assume dilset.l: |- L = ( Dil ` K )

  disjoint K x
  disjoint S x
  disjoint D x
  disjoint F x
  disjoint d k
  disjoint A k
  disjoint A d
  disjoint d f
  disjoint d x
  disjoint K d
  disjoint f k
  disjoint f x
  disjoint K f
  disjoint k x
  disjoint K k
  disjoint M f
  disjoint M k
  disjoint S k
  disjoint W k
  disjoint D d
  disjoint D f
  disjoint M d
  disjoint S d
  disjoint W d
  disjoint F f
  disjoint S f
  disjoint W f
  assert |- ( ( K e. B /\ D e. A ) -> ( F e. ( L ` D ) <-> ( F e. M /\ A. x e. S ( x C_ ( W ` D ) -> ( F ` x ) = x ) ) ) )

  proof
    cK
    cB
    wcel
    cD
    cA
    wcel
    wa
    #
    cF
    cD
    cL
    cfv
    #
    wcel
    cF
    vx
    cv
    #
    cD
    cW
    cfv
    wss
    #
    @2
    vf
    cv
    #
    cfv
    #
    @2
    wceq
    #
    wi
    #
    vx
    cS
    wral
    #
    vf
    cM
    crab
    #
    wcel
    cF
    cM
    wcel
    @3
    @2
    cF
    cfv
    #
    @2
    wceq
    #
    wi
    #
    vx
    cS
    wral
    #
    wa
    @0
    @1
    @9
    cF
    vx
    cA
    cB
    cD
    cS
    vf
    cK
    cL
    cM
    cW
    dilset.a
    dilset.s
    dilset.w
    dilset.m
    dilset.l
    dilsetN
    eleq2d
    @8
    @13
    vf
    cF
    cM
    @4
    cF
    wceq
    #
    @7
    @12
    vx
    cS
    @14
    @6
    @11
    @3
    @14
    @5
    @10
    @2
    @2
    @4
    cF
    fveq1
    eqeq1d
    imbi2d
    ralbidv
    elrab
    syl6bb
end
