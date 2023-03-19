include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "csn.mm"
include "cin.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "cmpt.mm"
include "trnfsetN.mm"
include "fveq1d.mm"
include "fveq2.mm"
include "sneq.mm"
include "fveq2d.mm"
include "ineq2d.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "eqid.mm"
include "fvex.mm"
include "rabex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem trnsetN
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let vf: setvar f
  let cK: class K
  let cL: class L
  let cM: class M
  let c.pe: class ._|_
  let cW: class W
  let vr: setvar r
  let vq: setvar q
  let vd: setvar d
  let vk: setvar k
  assume trnset.a: |- A = ( Atoms ` K )
  assume trnset.s: |- S = ( PSubSp ` K )
  assume trnset.p: |- .+ = ( +P ` K )
  assume trnset.o: |- ._|_ = ( _|_P ` K )
  assume trnset.w: |- W = ( WAtoms ` K )
  assume trnset.m: |- M = ( PAut ` K )
  assume trnset.l: |- L = ( Dil ` K )
  assume trnset.t: |- T = ( Trn ` K )

  disjoint f q
  disjoint f r
  disjoint K f
  disjoint q r
  disjoint K q
  disjoint K r
  disjoint L f
  disjoint W q
  disjoint W r
  disjoint D f
  disjoint D q
  disjoint D r
  disjoint d k
  disjoint A d
  disjoint A k
  disjoint d f
  disjoint d q
  disjoint d r
  disjoint K d
  disjoint f k
  disjoint k q
  disjoint k r
  disjoint K k
  disjoint L k
  disjoint ._|_ k
  disjoint .+ k
  disjoint W k
  disjoint D d
  disjoint L d
  disjoint ._|_ d
  disjoint .+ d
  disjoint W d
  assert |- ( ( K e. B /\ D e. A ) -> ( T ` D ) = { f e. ( L ` D ) | A. q e. ( W ` D ) A. r e. ( W ` D ) ( ( q .+ ( f ` q ) ) i^i ( ._|_ ` { D } ) ) = ( ( r .+ ( f ` r ) ) i^i ( ._|_ ` { D } ) ) } )

  proof
    cK
    cB
    wcel
    #
    cD
    cA
    wcel
    cD
    cT
    cfv
    cD
    vd
    cA
    vq
    cv
    #
    @1
    vf
    cv
    #
    cfv
    c.pl
    co
    #
    vd
    cv
    #
    csn
    #
    c.pe
    cfv
    #
    cin
    #
    vr
    cv
    #
    @8
    @2
    cfv
    c.pl
    co
    #
    @6
    cin
    #
    wceq
    #
    vr
    @4
    cW
    cfv
    #
    wral
    #
    vq
    @12
    wral
    #
    vf
    @4
    cL
    cfv
    #
    crab
    #
    cmpt
    #
    cfv
    @3
    cD
    csn
    #
    c.pe
    cfv
    #
    cin
    #
    @9
    @19
    cin
    #
    wceq
    #
    vr
    cD
    cW
    cfv
    #
    wral
    #
    vq
    @23
    wral
    #
    vf
    cD
    cL
    cfv
    #
    crab
    #
    @0
    cD
    cT
    @17
    cA
    cB
    c.pl
    cS
    cT
    vf
    cK
    cL
    cM
    c.pe
    cW
    vr
    vq
    vd
    trnset.a
    trnset.s
    trnset.p
    trnset.o
    trnset.w
    trnset.m
    trnset.l
    trnset.t
    trnfsetN
    fveq1d
    vd
    cD
    @16
    @27
    cA
    @17
    @4
    cD
    wceq
    #
    @14
    @25
    vf
    @15
    @26
    @4
    cD
    cL
    fveq2
    @28
    @13
    @24
    vq
    @12
    @23
    @4
    cD
    cW
    fveq2
    #
    @28
    @11
    @22
    vr
    @12
    @23
    @29
    @28
    @7
    @20
    @10
    @21
    @28
    @6
    @19
    @3
    @28
    @5
    @18
    c.pe
    @4
    cD
    sneq
    fveq2d
    #
    ineq2d
    @28
    @6
    @19
    @9
    @30
    ineq2d
    eqeq12d
    raleqbidv
    raleqbidv
    rabeqbidv
    @17
    eqid
    @25
    vf
    @26
    cD
    cL
    fvex
    rabex
    fvmpt
    sylan9eq
end
