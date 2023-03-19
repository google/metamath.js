include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "cv.mm"
include "co.mm"
include "wa.mm"
include "crio.mm"
include "cif.mm"
include "chlt.mm"
include "eldifad.mm"
include "hdmap1val.mm"
include "hdmap1cbv.mm"
include "mapdhval.mm"
include "eqtr4d.mm"

theorem hdmap1valc
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
  let cF: class F
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cL: class L
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let vw: setvar w
  let vg: setvar g
  assume hdmap1valc.h: |- H = ( LHyp ` K )
  assume hdmap1valc.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1valc.v: |- V = ( Base ` U )
  assume hdmap1valc.s: |- .- = ( -g ` U )
  assume hdmap1valc.o: |- .0. = ( 0g ` U )
  assume hdmap1valc.n: |- N = ( LSpan ` U )
  assume hdmap1valc.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1valc.d: |- D = ( Base ` C )
  assume hdmap1valc.r: |- R = ( -g ` C )
  assume hdmap1valc.q: |- Q = ( 0g ` C )
  assume hdmap1valc.j: |- J = ( LSpan ` C )
  assume hdmap1valc.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1valc.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1valc.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1valc.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1valc.f: |- ( ph -> F e. D )
  assume hdmap1valc.y: |- ( ph -> Y e. V )
  assume hdmap1valc.l: |- L = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )

  disjoint .0. x
  disjoint h x
  disjoint D h
  disjoint D x
  disjoint J h
  disjoint J x
  disjoint M h
  disjoint M x
  disjoint .- h
  disjoint .- x
  disjoint N h
  disjoint N x
  disjoint R h
  disjoint R x
  disjoint Q x
  disjoint w x
  disjoint .0. w
  disjoint C g
  disjoint g h
  disjoint g w
  disjoint g x
  disjoint D g
  disjoint h w
  disjoint D w
  disjoint J g
  disjoint J w
  disjoint M g
  disjoint M w
  disjoint .- g
  disjoint .- w
  disjoint F g
  disjoint F w
  disjoint N g
  disjoint N w
  disjoint g ph
  disjoint R g
  disjoint R w
  disjoint Q w
  disjoint U g
  disjoint V g
  disjoint X g
  disjoint X w
  disjoint Y g
  disjoint Y w
  assert |- ( ph -> ( I ` <. X , F , Y >. ) = ( L ` <. X , F , Y >. ) )

  proof
    wph
    cX
    cF
    cY
    cotp
    #
    cI
    cfv
    cY
    c.0
    wceq
    cQ
    cY
    csn
    cN
    cfv
    cM
    cfv
    vg
    cv
    #
    csn
    cJ
    cfv
    wceq
    cX
    cY
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    cF
    @1
    cR
    co
    csn
    cJ
    cfv
    wceq
    wa
    vg
    cD
    crio
    cif
    @0
    cL
    cfv
    wph
    chlt
    cC
    cD
    cQ
    cR
    cU
    vg
    cF
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cX
    cY
    c.0
    hdmap1valc.h
    hdmap1valc.u
    hdmap1valc.v
    hdmap1valc.s
    hdmap1valc.o
    hdmap1valc.n
    hdmap1valc.c
    hdmap1valc.d
    hdmap1valc.r
    hdmap1valc.q
    hdmap1valc.j
    hdmap1valc.m
    hdmap1valc.i
    hdmap1valc.k
    wph
    cX
    cV
    c.0
    csn
    hdmap1valc.x
    eldifad
    #
    hdmap1valc.f
    hdmap1valc.y
    hdmap1val
    wph
    vw
    cV
    cD
    cC
    cD
    cQ
    cR
    vg
    cV
    cF
    cL
    cJ
    cM
    c.mi
    cN
    cX
    cY
    c.0
    hdmap1valc.q
    vx
    vw
    cD
    cQ
    cR
    vh
    vg
    cJ
    cL
    cM
    c.mi
    cN
    c.0
    hdmap1valc.l
    hdmap1cbv
    @2
    hdmap1valc.f
    hdmap1valc.y
    mapdhval
    eqtr4d
end
