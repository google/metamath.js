include "wcel.mm"
include "cv.mm"
include "cdvh.mm"
include "cfv.mm"
include "clss.mm"
include "clk.mm"
include "coch.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "clfn.mm"
include "crab.mm"
include "cmpt.mm"
include "cmpd.mm"
include "mapdffval.mm"
include "fveq1d.mm"
include "syl5eq.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "fveq12d.mm"
include "eqeq12d.mm"
include "sseq1d.mm"
include "anbi12d.mm"
include "rabeqbidv.mm"
include "mpteq12dv.mm"
include "eqid.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"

theorem mapdfval
  let cS: class S
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cW: class W
  let cX: class X
  let vs: setvar s
  let vk: setvar k
  let vw: setvar w
  assume mapdval.h: |- H = ( LHyp ` K )
  assume mapdval.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdval.s: |- S = ( LSubSp ` U )
  assume mapdval.f: |- F = ( LFnl ` U )
  assume mapdval.l: |- L = ( LKer ` U )
  assume mapdval.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdval.m: |- M = ( ( mapd ` K ) ` W )

  disjoint f s
  disjoint K f
  disjoint K s
  disjoint F f
  disjoint S s
  disjoint W f
  disjoint W s
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f w
  disjoint k s
  disjoint K k
  disjoint s w
  disjoint K w
  disjoint F w
  disjoint L w
  disjoint O w
  disjoint S w
  disjoint W w
  assert |- ( ( K e. X /\ W e. H ) -> M = ( s e. S |-> { f e. F | ( ( O ` ( O ` ( L ` f ) ) ) = ( L ` f ) /\ ( O ` ( L ` f ) ) C_ s ) } ) )

  proof
    cK
    cX
    wcel
    #
    cW
    cH
    wcel
    cM
    cW
    vw
    cH
    vs
    vw
    cv
    #
    cK
    cdvh
    cfv
    #
    cfv
    #
    clss
    cfv
    #
    vf
    cv
    #
    @3
    clk
    cfv
    #
    cfv
    #
    @1
    cK
    coch
    cfv
    #
    cfv
    #
    cfv
    #
    @9
    cfv
    #
    @7
    wceq
    #
    @10
    vs
    cv
    #
    wss
    #
    wa
    #
    vf
    @3
    clfn
    cfv
    #
    crab
    #
    cmpt
    #
    cmpt
    #
    cfv
    #
    vs
    cS
    @5
    cL
    cfv
    #
    cO
    cfv
    #
    cO
    cfv
    #
    @21
    wceq
    #
    @22
    @13
    wss
    #
    wa
    #
    vf
    cF
    crab
    #
    cmpt
    #
    @0
    cM
    cW
    cK
    cmpd
    cfv
    #
    cfv
    @20
    mapdval.m
    @0
    cW
    @29
    @19
    vw
    vf
    cH
    cK
    cX
    vs
    mapdval.h
    mapdffval
    fveq1d
    syl5eq
    vw
    cW
    @18
    @28
    cH
    @19
    @1
    cW
    wceq
    #
    vs
    @4
    @17
    cS
    @27
    @30
    @4
    cU
    clss
    cfv
    #
    cS
    @30
    @3
    cU
    clss
    @30
    @3
    cW
    @2
    cfv
    cU
    @1
    cW
    @2
    fveq2
    mapdval.u
    syl6eqr
    #
    fveq2d
    mapdval.s
    syl6eqr
    @30
    @15
    @26
    vf
    @16
    cF
    @30
    @16
    cU
    clfn
    cfv
    cF
    @30
    @3
    cU
    clfn
    @32
    fveq2d
    mapdval.f
    syl6eqr
    @30
    @12
    @24
    @14
    @25
    @30
    @11
    @23
    @7
    @21
    @30
    @10
    @22
    @9
    cO
    @30
    @9
    cW
    @8
    cfv
    cO
    @1
    cW
    @8
    fveq2
    mapdval.o
    syl6eqr
    #
    @30
    @7
    @21
    @9
    cO
    @33
    @30
    @5
    @6
    cL
    @30
    @6
    cU
    clk
    cfv
    cL
    @30
    @3
    cU
    clk
    @32
    fveq2d
    mapdval.l
    syl6eqr
    fveq1d
    #
    fveq12d
    #
    fveq12d
    @34
    eqeq12d
    @30
    @10
    @22
    @13
    @35
    sseq1d
    anbi12d
    rabeqbidv
    mpteq12dv
    @19
    eqid
    vs
    cS
    @27
    cS
    @31
    cvv
    mapdval.s
    cU
    clss
    fvex
    eqeltri
    mptex
    fvmpt
    sylan9eq
end
