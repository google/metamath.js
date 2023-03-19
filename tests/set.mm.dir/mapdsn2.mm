include "csn.mm"
include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "mapdsn.mm"
include "sseq1d.mm"
include "rabbidv.mm"
include "eqtr4d.mm"

theorem mapdsn2
  let wph: wff ph
  let cU: class U
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  assume mapdsn.h: |- H = ( LHyp ` K )
  assume mapdsn.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdsn.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdsn.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdsn.v: |- V = ( Base ` U )
  assume mapdsn.n: |- N = ( LSpan ` U )
  assume mapdsn.f: |- F = ( LFnl ` U )
  assume mapdsn.l: |- L = ( LKer ` U )
  assume mapdsn.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdsn.x: |- ( ph -> X e. V )
  assume mapdsn2.e: |- ( ph -> ( L ` G ) = ( O ` { X } ) )

  disjoint F f
  disjoint K f
  disjoint N f
  disjoint W f
  disjoint X f
  disjoint f ph
  assert |- ( ph -> ( M ` ( N ` { X } ) ) = { f e. F | ( L ` G ) C_ ( L ` f ) } )

  proof
    wph
    cX
    csn
    #
    cN
    cfv
    cM
    cfv
    @0
    cO
    cfv
    #
    vf
    cv
    cL
    cfv
    #
    wss
    #
    vf
    cF
    crab
    cG
    cL
    cfv
    #
    @2
    wss
    #
    vf
    cF
    crab
    wph
    cU
    vf
    cF
    cH
    cK
    cL
    cM
    cN
    cO
    cV
    cW
    cX
    mapdsn.h
    mapdsn.o
    mapdsn.m
    mapdsn.u
    mapdsn.v
    mapdsn.n
    mapdsn.f
    mapdsn.l
    mapdsn.k
    mapdsn.x
    mapdsn
    wph
    @5
    @3
    vf
    cF
    wph
    @4
    @1
    @2
    mapdsn2.e
    sseq1d
    rabbidv
    eqtr4d
end
