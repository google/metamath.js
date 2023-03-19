include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "co.mm"
include "csn.mm"
include "cin.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "trnsetN.mm"
include "eleq2d.mm"
include "fveq1.mm"
include "oveq2d.mm"
include "ineq1d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "elrab.mm"
include "syl6bb.mm"

theorem istrnN
  let cA: class A
  let cB: class B
  let cD: class D
  let c.pl: class .+
  let cS: class S
  let cT: class T
  let cF: class F
  let cK: class K
  let cL: class L
  let cM: class M
  let c.pe: class ._|_
  let cW: class W
  let vr: setvar r
  let vq: setvar q
  let vd: setvar d
  let vk: setvar k
  let vf: setvar f
  assume trnset.a: |- A = ( Atoms ` K )
  assume trnset.s: |- S = ( PSubSp ` K )
  assume trnset.p: |- .+ = ( +P ` K )
  assume trnset.o: |- ._|_ = ( _|_P ` K )
  assume trnset.w: |- W = ( WAtoms ` K )
  assume trnset.m: |- M = ( PAut ` K )
  assume trnset.l: |- L = ( Dil ` K )
  assume trnset.t: |- T = ( Trn ` K )

  disjoint q r
  disjoint K q
  disjoint K r
  disjoint W q
  disjoint W r
  disjoint D q
  disjoint D r
  disjoint F q
  disjoint F r
  disjoint d k
  disjoint A d
  disjoint A k
  disjoint d f
  disjoint d q
  disjoint d r
  disjoint K d
  disjoint f k
  disjoint f q
  disjoint f r
  disjoint K f
  disjoint k q
  disjoint k r
  disjoint K k
  disjoint L f
  disjoint L k
  disjoint ._|_ k
  disjoint .+ k
  disjoint W k
  disjoint D d
  disjoint D f
  disjoint L d
  disjoint ._|_ d
  disjoint .+ d
  disjoint W d
  disjoint F f
  disjoint ._|_ f
  disjoint .+ f
  disjoint W f
  assert |- ( ( K e. B /\ D e. A ) -> ( F e. ( T ` D ) <-> ( F e. ( L ` D ) /\ A. q e. ( W ` D ) A. r e. ( W ` D ) ( ( q .+ ( F ` q ) ) i^i ( ._|_ ` { D } ) ) = ( ( r .+ ( F ` r ) ) i^i ( ._|_ ` { D } ) ) ) ) )

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
    cT
    cfv
    #
    wcel
    cF
    vq
    cv
    #
    @2
    vf
    cv
    #
    cfv
    #
    c.pl
    co
    #
    cD
    csn
    c.pe
    cfv
    #
    cin
    #
    vr
    cv
    #
    @8
    @3
    cfv
    #
    c.pl
    co
    #
    @6
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
    vq
    @13
    wral
    #
    vf
    cD
    cL
    cfv
    #
    crab
    #
    wcel
    cF
    @15
    wcel
    @2
    @2
    cF
    cfv
    #
    c.pl
    co
    #
    @6
    cin
    #
    @8
    @8
    cF
    cfv
    #
    c.pl
    co
    #
    @6
    cin
    #
    wceq
    #
    vr
    @13
    wral
    vq
    @13
    wral
    #
    wa
    @0
    @1
    @16
    cF
    cA
    cB
    cD
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
    trnset.a
    trnset.s
    trnset.p
    trnset.o
    trnset.w
    trnset.m
    trnset.l
    trnset.t
    trnsetN
    eleq2d
    @14
    @24
    vf
    cF
    @15
    @3
    cF
    wceq
    #
    @12
    @23
    vq
    vr
    @13
    @13
    @25
    @7
    @19
    @11
    @22
    @25
    @5
    @18
    @6
    @25
    @4
    @17
    @2
    c.pl
    @2
    @3
    cF
    fveq1
    oveq2d
    ineq1d
    @25
    @10
    @21
    @6
    @25
    @9
    @20
    @8
    c.pl
    @8
    @3
    cF
    fveq1
    oveq2d
    ineq1d
    eqeq12d
    2ralbidv
    elrab
    syl6bb
end
