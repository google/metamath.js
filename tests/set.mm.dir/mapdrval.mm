include "cfv.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "chlt.mm"
include "lcfr.mm"
include "mapdvalc.mm"
include "clsa.mm"
include "clspn.mm"
include "cbs.mm"
include "c0g.mm"
include "ciun.mm"
include "weq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "cbviunv.mm"
include "eqtri.mm"
include "eqid.mm"
include "mapdrvallem3.mm"
include "eqtrd.mm"

theorem mapdrval
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cO: class O
  let cW: class W
  let vf: setvar f
  let vi: setvar i
  let cV: class V
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

  disjoint F g
  disjoint g h
  disjoint L g
  disjoint L h
  disjoint O g
  disjoint O h
  disjoint R h
  disjoint U g
  disjoint f i
  disjoint C f
  disjoint C i
  disjoint D i
  disjoint f g
  disjoint F f
  disjoint K f
  disjoint g i
  disjoint h i
  disjoint L i
  disjoint O i
  disjoint Q f
  disjoint Q i
  disjoint f h
  disjoint R f
  disjoint R i
  disjoint U i
  disjoint V i
  disjoint W f
  disjoint f ph
  disjoint i ph
  assert |- ( ph -> ( M ` Q ) = R )

  proof
    wph
    cQ
    cM
    cfv
    vf
    cv
    cL
    cfv
    cO
    cfv
    cQ
    wss
    vf
    cC
    crab
    cR
    wph
    cC
    cS
    cQ
    cU
    vf
    vg
    cF
    cH
    cK
    cL
    cM
    cO
    cW
    chlt
    mapdrval.h
    mapdrval.u
    mapdrval.s
    mapdrval.f
    mapdrval.l
    mapdrval.o
    mapdrval.m
    mapdrval.k
    wph
    cC
    cD
    cQ
    cR
    cS
    cT
    cU
    vg
    vh
    cF
    cH
    cK
    cL
    cO
    cW
    mapdrval.h
    mapdrval.o
    mapdrval.u
    mapdrval.s
    mapdrval.f
    mapdrval.l
    mapdrval.d
    mapdrval.t
    mapdrval.c
    mapdrval.q
    mapdrval.k
    mapdrval.r
    mapdrval.e
    lcfr
    mapdrval.c
    mapdvalc
    wph
    cU
    clsa
    cfv
    #
    cC
    cD
    cQ
    cR
    cS
    cT
    cU
    vf
    vg
    vi
    cF
    cH
    cK
    cL
    cM
    cU
    clspn
    cfv
    #
    cO
    cU
    cbs
    cfv
    #
    cW
    cD
    c0g
    cfv
    #
    cU
    c0g
    cfv
    #
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
    cQ
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
    vi
    cR
    vi
    cv
    #
    cL
    cfv
    #
    cO
    cfv
    #
    ciun
    mapdrval.q
    vh
    vi
    cR
    @7
    @10
    vh
    vi
    weq
    @6
    @9
    cO
    @5
    @8
    cL
    fveq2
    fveq2d
    cbviunv
    eqtri
    @2
    eqid
    @0
    eqid
    @1
    eqid
    @4
    eqid
    @3
    eqid
    mapdrvallem3
    eqtrd
end
