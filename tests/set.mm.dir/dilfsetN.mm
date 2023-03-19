include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "crab.mm"
include "cmpt.mm"
include "elex.mm"
include "cdilN.mm"
include "catm.mm"
include "cwpointsN.mm"
include "cpsubsp.mm"
include "cpautN.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "sseq2d.mm"
include "imbi1d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "df-dilN.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem dilfsetN
  let vx: setvar x
  let cA: class A
  let cB: class B
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

  disjoint A d
  disjoint d f
  disjoint d x
  disjoint K d
  disjoint f x
  disjoint K f
  disjoint K x
  disjoint M f
  disjoint S x
  disjoint d k
  disjoint A k
  disjoint f k
  disjoint k x
  disjoint K k
  disjoint M k
  disjoint S k
  disjoint W k
  assert |- ( K e. B -> L = ( d e. A |-> { f e. M | A. x e. S ( x C_ ( W ` d ) -> ( f ` x ) = x ) } ) )

  proof
    cK
    cB
    wcel
    cK
    cvv
    wcel
    #
    cL
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
    wceq
    cK
    cB
    elex
    @0
    cL
    cK
    cdilN
    cfv
    @9
    dilset.l
    vk
    cK
    vd
    vk
    cv
    #
    catm
    cfv
    #
    @1
    @2
    @10
    cwpointsN
    cfv
    #
    cfv
    #
    wss
    #
    @5
    wi
    #
    vx
    @10
    cpsubsp
    cfv
    #
    wral
    #
    vf
    @10
    cpautN
    cfv
    #
    crab
    #
    cmpt
    @9
    cvv
    cdilN
    @10
    cK
    wceq
    #
    vd
    @11
    @19
    cA
    @8
    @20
    @11
    cK
    catm
    cfv
    #
    cA
    @10
    cK
    catm
    fveq2
    dilset.a
    syl6eqr
    @20
    @17
    @7
    vf
    @18
    cM
    @20
    @18
    cK
    cpautN
    cfv
    cM
    @10
    cK
    cpautN
    fveq2
    dilset.m
    syl6eqr
    @20
    @15
    @6
    vx
    @16
    cS
    @20
    @16
    cK
    cpsubsp
    cfv
    cS
    @10
    cK
    cpsubsp
    fveq2
    dilset.s
    syl6eqr
    @20
    @14
    @4
    @5
    @20
    @13
    @3
    @1
    @20
    @2
    @12
    cW
    @20
    @12
    cK
    cwpointsN
    cfv
    cW
    @10
    cK
    cwpointsN
    fveq2
    dilset.w
    syl6eqr
    fveq1d
    sseq2d
    imbi1d
    raleqbidv
    rabeqbidv
    mpteq12dv
    vx
    vf
    vk
    vd
    df-dilN
    vd
    cA
    @8
    cA
    @21
    cvv
    dilset.a
    cK
    catm
    fvex
    eqeltri
    mptex
    fvmpt
    syl5eq
    syl
end
