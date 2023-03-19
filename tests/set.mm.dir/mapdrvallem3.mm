include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "crab.mm"
include "mapdrvallem2.mm"
include "wcel.mm"
include "wa.mm"
include "ciun.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "ssiun2s.mm"
include "adantl.mm"
include "syl6sseqr.mm"
include "ssrabdv.mm"
include "eqssd.mm"

theorem mapdrvallem3
  let wph: wff ph
  let cA: class A
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cY: class Y
  let c.0: class .0.
  let vr: setvar r
  let vx: setvar x
  let vi: setvar i
  assume mapdrval.h: |- H = ( LHyp ` K )
  assume mapdrval.o: |- O = ( ( ocH ` K ) ` W )
  assume mapdrval.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdrval.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdrval.s: |- S = ( LSubSp ` U )
  assume mapdrval.f: |- F = ( LFnl ` U )
  assume mapdrval.l: |- L = ( LKer ` U )
  assume mapdrval.d: |- D = ( LDual ` U )
  assume mapdrval.t: |- T = ( LSubSp ` D )
  assume mapdrval.c: |- C = { g e. F | ( O ` ( O ` ( L ` g ) ) ) = ( L ` g ) }
  assume mapdrval.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdrval.r: |- ( ph -> R e. T )
  assume mapdrval.e: |- ( ph -> R C_ C )
  assume mapdrval.q: |- Q = U_ h e. R ( O ` ( L ` h ) )
  assume mapdrval.v: |- V = ( Base ` U )
  assume mapdrvallem2.a: |- A = ( LSAtoms ` U )
  assume mapdrvallem2.n: |- N = ( LSpan ` U )
  assume mapdrvallem2.z: |- .0. = ( 0g ` U )
  assume mapdrvallem2.y: |- Y = ( 0g ` D )

  disjoint C h
  disjoint N h
  disjoint Q h
  disjoint U h
  disjoint V h
  disjoint Y h
  disjoint .0. h
  disjoint h ph
  disjoint f g
  disjoint C f
  disjoint f g
  disjoint F f
  disjoint F g
  disjoint K f
  disjoint g h
  disjoint L g
  disjoint L h
  disjoint O g
  disjoint O h
  disjoint Q f
  disjoint f h
  disjoint R f
  disjoint R h
  disjoint U g
  disjoint W f
  disjoint f ph
  disjoint h r
  disjoint h x
  disjoint r x
  disjoint C r
  disjoint C x
  disjoint F r
  disjoint L r
  disjoint L x
  disjoint N r
  disjoint O r
  disjoint O x
  disjoint Q r
  disjoint Q x
  disjoint R r
  disjoint R x
  disjoint U r
  disjoint U x
  disjoint V r
  disjoint V x
  disjoint Y r
  disjoint Y x
  disjoint .0. r
  disjoint ph r
  disjoint ph x
  disjoint f r
  disjoint f x
  disjoint g r
  disjoint g x
  disjoint f i
  disjoint C i
  disjoint D i
  disjoint g i
  disjoint h i
  disjoint L i
  disjoint O i
  disjoint Q i
  disjoint R i
  disjoint U i
  disjoint V i
  disjoint i ph
  assert |- ( ph -> { f e. C | ( O ` ( L ` f ) ) C_ Q } = R )

  proof
    wph
    vf
    cv
    #
    cL
    cfv
    #
    cO
    cfv
    #
    cQ
    wss
    #
    vf
    cC
    crab
    cR
    wph
    cA
    cC
    cD
    cQ
    cR
    cS
    cT
    cU
    vf
    vg
    vh
    cF
    cH
    cK
    cL
    cM
    cN
    cO
    cV
    cW
    cY
    c.0
    mapdrval.h
    mapdrval.o
    mapdrval.m
    mapdrval.u
    mapdrval.s
    mapdrval.f
    mapdrval.l
    mapdrval.d
    mapdrval.t
    mapdrval.c
    mapdrval.k
    mapdrval.r
    mapdrval.e
    mapdrval.q
    mapdrval.v
    mapdrvallem2.a
    mapdrvallem2.n
    mapdrvallem2.z
    mapdrvallem2.y
    mapdrvallem2
    wph
    @3
    vf
    cC
    cR
    mapdrval.e
    wph
    @0
    cR
    wcel
    #
    wa
    @2
    vh
    cR
    vh
    cv
    #
    cL
    cfv
    #
    cO
    cfv
    #
    ciun
    #
    cQ
    @4
    @2
    @8
    wss
    wph
    vh
    cR
    @7
    @0
    @2
    vh
    vf
    weq
    @6
    @1
    cO
    @5
    @0
    cL
    fveq2
    fveq2d
    ssiun2s
    adantl
    mapdrval.q
    syl6sseqr
    ssrabdv
    eqssd
end
