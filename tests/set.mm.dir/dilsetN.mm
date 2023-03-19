include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cmpt.mm"
include "dilfsetN.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rabbidv.mm"
include "eqid.mm"
include "cpautN.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem dilsetN
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let vf: setvar f
  let cK: class K
  let cL: class L
  let cM: class M
  let cW: class W
  let vd: setvar d
  let vk: setvar k
  assume dilset.a: |- A = ( Atoms ` K )
  assume dilset.s: |- S = ( PSubSp ` K )
  assume dilset.w: |- W = ( WAtoms ` K )
  assume dilset.m: |- M = ( PAut ` K )
  assume dilset.l: |- L = ( Dil ` K )

  disjoint f x
  disjoint K f
  disjoint K x
  disjoint M f
  disjoint S x
  disjoint D f
  disjoint D x
  disjoint d k
  disjoint A k
  disjoint A d
  disjoint d f
  disjoint d x
  disjoint K d
  disjoint f k
  disjoint k x
  disjoint K k
  disjoint M k
  disjoint S k
  disjoint W k
  disjoint D d
  disjoint M d
  disjoint S d
  disjoint W d
  assert |- ( ( K e. B /\ D e. A ) -> ( L ` D ) = { f e. M | A. x e. S ( x C_ ( W ` D ) -> ( f ` x ) = x ) } )

  proof
    cK
    cB
    wcel
    #
    cD
    cA
    wcel
    cD
    cL
    cfv
    cD
    vd
    cA
    vx
    cv
    #
    vd
    cv
    #
    cW
    cfv
    #
    wss
    #
    @1
    vf
    cv
    cfv
    @1
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
    cmpt
    #
    cfv
    @1
    cD
    cW
    cfv
    #
    wss
    #
    @5
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
    @0
    cD
    cL
    @9
    vx
    cA
    cB
    cS
    vf
    cK
    cL
    cM
    cW
    vd
    dilset.a
    dilset.s
    dilset.w
    dilset.m
    dilset.l
    dilfsetN
    fveq1d
    vd
    cD
    @8
    @14
    cA
    @9
    @2
    cD
    wceq
    #
    @7
    @13
    vf
    cM
    @15
    @6
    @12
    vx
    cS
    @15
    @4
    @11
    @5
    @15
    @3
    @10
    @1
    @2
    cD
    cW
    fveq2
    sseq2d
    imbi1d
    ralbidv
    rabbidv
    @9
    eqid
    @13
    vf
    cM
    cM
    cK
    cpautN
    cfv
    cvv
    dilset.m
    cK
    cpautN
    fvex
    eqeltri
    rabex
    fvmpt
    sylan9eq
end
