include "wcel.mm"
include "cvv.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "cin.mm"
include "wceq.mm"
include "wral.mm"
include "crab.mm"
include "cmpt.mm"
include "elex.mm"
include "ctrnN.mm"
include "catm.mm"
include "cpadd.mm"
include "cpolN.mm"
include "cwpointsN.mm"
include "cdilN.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq1d.mm"
include "oveqd.mm"
include "ineq12d.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "df-trnN.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "syl5eq.mm"
include "syl.mm"

theorem trnfsetN
  let cA: class A
  let cC: class C
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

  disjoint A d
  disjoint d f
  disjoint d q
  disjoint d r
  disjoint K d
  disjoint f q
  disjoint f r
  disjoint K f
  disjoint q r
  disjoint K q
  disjoint K r
  disjoint L f
  disjoint W q
  disjoint W r
  disjoint d k
  disjoint A k
  disjoint f k
  disjoint k q
  disjoint k r
  disjoint K k
  disjoint L k
  disjoint ._|_ k
  disjoint .+ k
  disjoint W k
  assert |- ( K e. C -> T = ( d e. A |-> { f e. ( L ` d ) | A. q e. ( W ` d ) A. r e. ( W ` d ) ( ( q .+ ( f ` q ) ) i^i ( ._|_ ` { d } ) ) = ( ( r .+ ( f ` r ) ) i^i ( ._|_ ` { d } ) ) } ) )

  proof
    cK
    cC
    wcel
    cK
    cvv
    wcel
    #
    cT
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
    #
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
    @9
    @2
    cfv
    #
    c.pl
    co
    #
    @7
    cin
    #
    wceq
    #
    vr
    @5
    cW
    cfv
    #
    wral
    #
    vq
    @14
    wral
    #
    vf
    @5
    cL
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
    @0
    cT
    cK
    ctrnN
    cfv
    @19
    trnset.t
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
    @3
    @20
    cpadd
    cfv
    #
    co
    #
    @6
    @20
    cpolN
    cfv
    #
    cfv
    #
    cin
    #
    @9
    @10
    @22
    co
    #
    @25
    cin
    #
    wceq
    #
    vr
    @5
    @20
    cwpointsN
    cfv
    #
    cfv
    #
    wral
    #
    vq
    @31
    wral
    #
    vf
    @5
    @20
    cdilN
    cfv
    #
    cfv
    #
    crab
    #
    cmpt
    @19
    cvv
    ctrnN
    @20
    cK
    wceq
    #
    vd
    @21
    @36
    cA
    @18
    @37
    @21
    cK
    catm
    cfv
    #
    cA
    @20
    cK
    catm
    fveq2
    trnset.a
    syl6eqr
    @37
    @33
    @16
    vf
    @35
    @17
    @37
    @5
    @34
    cL
    @37
    @34
    cK
    cdilN
    cfv
    cL
    @20
    cK
    cdilN
    fveq2
    trnset.l
    syl6eqr
    fveq1d
    @37
    @32
    @15
    vq
    @31
    @14
    @37
    @5
    @30
    cW
    @37
    @30
    cK
    cwpointsN
    cfv
    cW
    @20
    cK
    cwpointsN
    fveq2
    trnset.w
    syl6eqr
    fveq1d
    #
    @37
    @29
    @13
    vr
    @31
    @14
    @39
    @37
    @26
    @8
    @28
    @12
    @37
    @23
    @4
    @25
    @7
    @37
    @22
    c.pl
    @1
    @3
    @37
    @22
    cK
    cpadd
    cfv
    c.pl
    @20
    cK
    cpadd
    fveq2
    trnset.p
    syl6eqr
    #
    oveqd
    @37
    @6
    @24
    c.pe
    @37
    @24
    cK
    cpolN
    cfv
    c.pe
    @20
    cK
    cpolN
    fveq2
    trnset.o
    syl6eqr
    fveq1d
    #
    ineq12d
    @37
    @27
    @11
    @25
    @7
    @37
    @22
    c.pl
    @9
    @10
    @40
    oveqd
    @41
    ineq12d
    eqeq12d
    raleqbidv
    raleqbidv
    rabeqbidv
    mpteq12dv
    vf
    vk
    vr
    vq
    vd
    df-trnN
    vd
    cA
    @18
    cA
    @38
    cvv
    trnset.a
    cK
    catm
    fvex
    eqeltri
    mptex
    fvmpt
    syl5eq
    syl
end
