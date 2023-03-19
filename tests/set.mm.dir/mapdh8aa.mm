include "cotp.mm"
include "cfv.mm"
include "csn.mm"
include "eldifad.mm"
include "wne.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "mapdhcl.mm"
include "eqeltrrd.mm"
include "wceq.mm"
include "co.mm"
include "wa.mm"
include "mapdheq.mm"
include "mpbid.mm"
include "mapdh75d.mm"
include "mapdh8a.mm"
include "eqcomd.mm"

theorem mapdh8aa
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
  let cT: class T
  let cU: class U
  let vh: setvar h
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cK: class K
  let cM: class M
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume mapdh8a.h: |- H = ( LHyp ` K )
  assume mapdh8a.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh8a.v: |- V = ( Base ` U )
  assume mapdh8a.s: |- .- = ( -g ` U )
  assume mapdh8a.o: |- .0. = ( 0g ` U )
  assume mapdh8a.n: |- N = ( LSpan ` U )
  assume mapdh8a.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh8a.d: |- D = ( Base ` C )
  assume mapdh8a.r: |- R = ( -g ` C )
  assume mapdh8a.q: |- Q = ( 0g ` C )
  assume mapdh8a.j: |- J = ( LSpan ` C )
  assume mapdh8a.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh8a.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh8a.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdh8aa.f: |- ( ph -> F e. D )
  assume mapdh8aa.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh8aa.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh8aa.ee: |- ( ph -> ( I ` <. X , F , Z >. ) = E )
  assume mapdh8aa.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh8aa.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdh8aa.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdh8aa.zt: |- ( ph -> ( N ` { Z } ) =/= ( N ` { T } ) )
  assume mapdh8aa.t: |- ( ph -> T e. ( V \ { .0. } ) )
  assume mapdh8aa.yn: |- ( ph -> -. Y e. ( N ` { Z , T } ) )
  assume mapdh8aa.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )

  disjoint h x
  disjoint .- h
  disjoint .- x
  disjoint .0. h
  disjoint .0. x
  disjoint C h
  disjoint D h
  disjoint D x
  disjoint F h
  disjoint F x
  disjoint I h
  disjoint G h
  disjoint G x
  disjoint J h
  disjoint J x
  disjoint M h
  disjoint M x
  disjoint N h
  disjoint N x
  disjoint h ph
  disjoint R h
  disjoint R x
  disjoint Q x
  disjoint T h
  disjoint T x
  disjoint U h
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint E h
  disjoint E x
  disjoint Z h
  disjoint Z x
  assert |- ( ph -> ( I ` <. Y , G , T >. ) = ( I ` <. Z , E , T >. ) )

  proof
    wph
    cZ
    cE
    cT
    cotp
    cI
    cfv
    cY
    cG
    cT
    cotp
    cI
    cfv
    wph
    vx
    cC
    cD
    cQ
    cR
    cT
    cU
    vh
    cG
    cE
    cH
    cI
    cJ
    cK
    cM
    c.mi
    cN
    cV
    cW
    cY
    cZ
    c.0
    mapdh8a.h
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.q
    mapdh8a.j
    mapdh8a.m
    mapdh8a.i
    mapdh8a.k
    wph
    cX
    cF
    cY
    cotp
    cI
    cfv
    #
    cG
    cD
    mapdh8aa.eg
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
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
    mapdh8a.q
    mapdh8a.i
    mapdh8a.h
    mapdh8a.m
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.j
    mapdh8a.k
    mapdh8aa.f
    mapdh8aa.mn
    mapdh8aa.x
    wph
    cY
    cV
    c.0
    csn
    #
    mapdh8aa.y
    eldifad
    #
    wph
    cX
    csn
    cN
    cfv
    #
    cY
    csn
    cN
    cfv
    #
    wne
    @3
    cZ
    csn
    cN
    cfv
    #
    wne
    wph
    cN
    cV
    cU
    cX
    cY
    cZ
    mapdh8a.v
    mapdh8a.n
    wph
    cU
    cH
    cK
    cW
    mapdh8a.h
    mapdh8a.u
    mapdh8a.k
    dvhlvec
    #
    wph
    cX
    cV
    @1
    mapdh8aa.x
    eldifad
    @2
    wph
    cZ
    cV
    @1
    mapdh8aa.z
    eldifad
    #
    mapdh8aa.xn
    lspindpi
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    wph
    @4
    cM
    cfv
    cG
    csn
    cJ
    cfv
    wceq
    #
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
    cG
    cR
    co
    csn
    cJ
    cfv
    wceq
    #
    wph
    @0
    cG
    wceq
    @10
    @11
    wa
    mapdh8aa.eg
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
    cG
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
    mapdh8a.q
    mapdh8a.i
    mapdh8a.h
    mapdh8a.m
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.j
    mapdh8a.k
    mapdh8aa.f
    mapdh8aa.mn
    mapdh8aa.x
    mapdh8aa.y
    @9
    @8
    mapdheq
    mpbid
    simpld
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cE
    cF
    cG
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
    cZ
    mapdh8a.h
    mapdh8a.u
    mapdh8a.v
    mapdh8a.s
    mapdh8a.o
    mapdh8a.n
    mapdh8a.c
    mapdh8a.d
    mapdh8a.r
    mapdh8a.q
    mapdh8a.j
    mapdh8a.m
    mapdh8a.i
    mapdh8a.k
    mapdh8aa.f
    mapdh8aa.mn
    mapdh8aa.eg
    mapdh8aa.ee
    wph
    @4
    @5
    wne
    @4
    cT
    csn
    cN
    cfv
    wne
    wph
    cN
    cV
    cU
    cY
    cZ
    cT
    mapdh8a.v
    mapdh8a.n
    @6
    @2
    @7
    wph
    cT
    cV
    @1
    mapdh8aa.t
    eldifad
    mapdh8aa.yn
    lspindpi
    simpld
    mapdh8aa.xn
    mapdh8aa.x
    mapdh8aa.y
    mapdh8aa.z
    mapdh75d
    mapdh8aa.y
    mapdh8aa.z
    mapdh8aa.zt
    mapdh8aa.t
    mapdh8aa.yn
    mapdh8a
    eqcomd
end
