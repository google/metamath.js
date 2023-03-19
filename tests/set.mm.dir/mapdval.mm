include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "crab.mm"
include "cmpt.mm"
include "wcel.mm"
include "mapdfval.mm"
include "syl.mm"
include "fveq1d.mm"
include "cvv.mm"
include "clfn.mm"
include "fvex.mm"
include "eqeltri.mm"
include "rabex.mm"
include "sseq2.mm"
include "anbi2d.mm"
include "rabbidv.mm"
include "eqid.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "eqtrd.mm"

theorem mapdval
  let wph: wff ph
  let cS: class S
  let cT: class T
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
  let vk: setvar k
  let vw: setvar w
  let vs: setvar s
  let vg: setvar g
  assume mapdval.h: |- H = ( LHyp ` K )
  assume mapdval.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdval.s: |- S = ( LSubSp ` U )
  assume mapdval.f: |- F = ( LFnl ` U )
  assume mapdval.l: |- L = ( LKer ` U )
  assume mapdval.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdval.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdval.k: |- ( ph -> ( K e. X /\ W e. H ) )
  assume mapdval.t: |- ( ph -> T e. S )

  disjoint K f
  disjoint F f
  disjoint W f
  disjoint T f
  disjoint k w
  disjoint H k
  disjoint H w
  disjoint f k
  disjoint f s
  disjoint f w
  disjoint k s
  disjoint K k
  disjoint s w
  disjoint K s
  disjoint K w
  disjoint F w
  disjoint L w
  disjoint O w
  disjoint S s
  disjoint S w
  disjoint W s
  disjoint W w
  disjoint f g
  disjoint g s
  disjoint F g
  disjoint F s
  disjoint L g
  disjoint L s
  disjoint O g
  disjoint O s
  disjoint T s
  assert |- ( ph -> ( M ` T ) = { f e. F | ( ( O ` ( O ` ( L ` f ) ) ) = ( L ` f ) /\ ( O ` ( L ` f ) ) C_ T ) } )

  proof
    wph
    cT
    cM
    cfv
    cT
    vs
    cS
    vf
    cv
    cL
    cfv
    #
    cO
    cfv
    #
    cO
    cfv
    @0
    wceq
    #
    @1
    vs
    cv
    #
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
    cfv
    #
    @2
    @1
    cT
    wss
    #
    wa
    #
    vf
    cF
    crab
    #
    wph
    cT
    cM
    @7
    wph
    cK
    cX
    wcel
    cW
    cH
    wcel
    wa
    cM
    @7
    wceq
    mapdval.k
    cS
    cU
    vf
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    cX
    vs
    mapdval.h
    mapdval.u
    mapdval.s
    mapdval.f
    mapdval.l
    mapdval.o
    mapdval.m
    mapdfval
    syl
    fveq1d
    wph
    cT
    cS
    wcel
    @11
    cvv
    wcel
    @8
    @11
    wceq
    mapdval.t
    @10
    vf
    cF
    cF
    cU
    clfn
    cfv
    cvv
    mapdval.f
    cU
    clfn
    fvex
    eqeltri
    rabex
    vs
    cT
    @6
    @11
    cS
    cvv
    @7
    @3
    cT
    wceq
    #
    @5
    @10
    vf
    cF
    @12
    @4
    @9
    @2
    @3
    cT
    @1
    sseq2
    anbi2d
    rabbidv
    @7
    eqid
    fvmptg
    sylancl
    eqtrd
end
