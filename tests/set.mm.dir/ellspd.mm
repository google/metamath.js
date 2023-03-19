include "cima.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "cof.mm"
include "co.mm"
include "cgsu.mm"
include "wceq.mm"
include "cfrlm.mm"
include "cbs.mm"
include "wrex.mm"
include "cab.mm"
include "cfsupp.mm"
include "wbr.mm"
include "wa.mm"
include "cmap.mm"
include "crn.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "fnima.mm"
include "3syl.mm"
include "fveq2d.mm"
include "cmpt.mm"
include "eqid.mm"
include "rnmpt.mm"
include "cvv.mm"
include "csca.mm"
include "a1i.mm"
include "frlmup3.mm"
include "syl5eqr.mm"
include "eqtr4d.mm"
include "eleq2d.mm"
include "ovex.mm"
include "eleq1.mm"
include "mpbiri.mm"
include "rexlimivw.mm"
include "eqeq1.mm"
include "rexbidv.mm"
include "elab3.mm"
include "crab.mm"
include "fvex.mm"
include "eqeltri.mm"
include "frlmbas.mm"
include "sylancr.mm"
include "eqcomd.mm"
include "rexeqdv.mm"
include "breq1.mm"
include "rexrab.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "bitrd.mm"

theorem ellspd
  let wph: wff ph
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let vf: setvar f
  let cF: class F
  let cI: class I
  let cK: class K
  let cM: class M
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let va: setvar a
  assume ellspd.n: |- N = ( LSpan ` M )
  assume ellspd.v: |- B = ( Base ` M )
  assume ellspd.k: |- K = ( Base ` S )
  assume ellspd.s: |- S = ( Scalar ` M )
  assume ellspd.z: |- .0. = ( 0g ` S )
  assume ellspd.t: |- .x. = ( .s ` M )
  assume ellspd.f: |- ( ph -> F : I --> B )
  assume ellspd.m: |- ( ph -> M e. LMod )
  assume ellspd.i: |- ( ph -> I e. _V )

  disjoint M f
  disjoint B f
  disjoint N f
  disjoint K f
  disjoint S f
  disjoint .0. f
  disjoint .x. f
  disjoint F f
  disjoint I f
  disjoint X f
  disjoint f ph
  disjoint M a
  disjoint a f
  disjoint B a
  disjoint N a
  disjoint K a
  disjoint S a
  disjoint .0. a
  disjoint .x. a
  disjoint F a
  disjoint I a
  disjoint X a
  disjoint a ph
  assert |- ( ph -> ( X e. ( N ` ( F " I ) ) <-> E. f e. ( K ^m I ) ( f finSupp .0. /\ X = ( M gsum ( f oF .x. F ) ) ) ) )

  proof
    wph
    cX
    cF
    cI
    cima
    #
    cN
    cfv
    #
    wcel
    cX
    va
    cv
    #
    cM
    vf
    cv
    #
    cF
    c.x
    cof
    co
    #
    cgsu
    co
    #
    wceq
    #
    vf
    cS
    cI
    cfrlm
    co
    #
    cbs
    cfv
    #
    wrex
    #
    va
    cab
    #
    wcel
    #
    @3
    c.0
    cfsupp
    wbr
    #
    cX
    @5
    wceq
    #
    wa
    vf
    cK
    cI
    cmap
    co
    #
    wrex
    #
    wph
    @1
    @10
    cX
    wph
    @1
    cF
    crn
    #
    cN
    cfv
    #
    @10
    wph
    @0
    @16
    cN
    wph
    cI
    cB
    cF
    wf
    cF
    cI
    wfn
    @0
    @16
    wceq
    ellspd.f
    cI
    cB
    cF
    ffn
    cI
    cF
    fnima
    3syl
    fveq2d
    wph
    @10
    vf
    @8
    @5
    cmpt
    #
    crn
    @17
    vf
    va
    @8
    @5
    @18
    @18
    eqid
    #
    rnmpt
    wph
    vf
    cF
    @8
    cB
    cS
    cM
    c.x
    @18
    @7
    cI
    cN
    cvv
    @7
    eqid
    #
    @8
    eqid
    ellspd.v
    ellspd.t
    @19
    ellspd.m
    ellspd.i
    cS
    cM
    csca
    cfv
    #
    wceq
    wph
    ellspd.s
    a1i
    ellspd.f
    ellspd.n
    frlmup3
    syl5eqr
    eqtr4d
    eleq2d
    @11
    @13
    vf
    @8
    wrex
    #
    wph
    @15
    @9
    @22
    va
    cX
    @13
    cX
    cvv
    wcel
    #
    vf
    @8
    @13
    @23
    @5
    cvv
    wcel
    cM
    @4
    cgsu
    ovex
    cX
    @5
    cvv
    eleq1
    mpbiri
    rexlimivw
    @2
    cX
    wceq
    @6
    @13
    vf
    @8
    @2
    cX
    @5
    eqeq1
    rexbidv
    elab3
    wph
    @22
    @13
    vf
    @2
    c.0
    cfsupp
    wbr
    #
    va
    @14
    crab
    #
    wrex
    @15
    wph
    @13
    vf
    @8
    @25
    wph
    @25
    @8
    wph
    cS
    cvv
    wcel
    cI
    cvv
    wcel
    @25
    @8
    wceq
    cS
    @21
    cvv
    ellspd.s
    cM
    csca
    fvex
    eqeltri
    ellspd.i
    @25
    cS
    va
    @7
    cI
    cK
    cvv
    cvv
    c.0
    @20
    ellspd.k
    ellspd.z
    @25
    eqid
    frlmbas
    sylancr
    eqcomd
    rexeqdv
    @24
    @12
    @13
    vf
    va
    @14
    @2
    @3
    c.0
    cfsupp
    breq1
    rexrab
    syl6bb
    syl5bb
    bitrd
end
