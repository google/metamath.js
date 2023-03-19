include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "co.mm"
include "wa.mm"
include "eldifad.mm"
include "wne.mm"
include "cpr.mm"
include "wcel.mm"
include "wn.mm"
include "dvhlvec.mm"
include "lspindp1.mm"
include "simpld.mm"
include "mapdhcl.mm"
include "eqeltrrd.mm"
include "mapdheq.mm"
include "mpbid.mm"
include "mapdheq4lem.mm"
include "lspindp2.mm"
include "mpbir2and.mm"

theorem mapdheq4
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let cQ: class Q
  let cR: class R
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
  let vw: setvar w
  assume mapdh.q: |- Q = ( 0g ` C )
  assume mapdh.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh.h: |- H = ( LHyp ` K )
  assume mapdh.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh.v: |- V = ( Base ` U )
  assume mapdh.s: |- .- = ( -g ` U )
  assume mapdhc.o: |- .0. = ( 0g ` U )
  assume mapdh.n: |- N = ( LSpan ` U )
  assume mapdh.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh.d: |- D = ( Base ` C )
  assume mapdh.r: |- R = ( -g ` C )
  assume mapdh.j: |- J = ( LSpan ` C )
  assume mapdh.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdhc.f: |- ( ph -> F e. D )
  assume mapdh.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdhcl.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdhe4.y: |- ( ph -> Y e. ( V \ { .0. } ) )
  assume mapdhe.z: |- ( ph -> Z e. ( V \ { .0. } ) )
  assume mapdh.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume mapdh.yz: |- ( ph -> ( N ` { Y } ) =/= ( N ` { Z } ) )
  assume mapdh.eg: |- ( ph -> ( I ` <. X , F , Y >. ) = G )
  assume mapdh.ee: |- ( ph -> ( I ` <. X , F , Z >. ) = E )

  disjoint D x
  disjoint h x
  disjoint F h
  disjoint F x
  disjoint J x
  disjoint M x
  disjoint N x
  disjoint .0. x
  disjoint Q x
  disjoint R x
  disjoint .- x
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint h ph
  disjoint .0. h
  disjoint C h
  disjoint D h
  disjoint J h
  disjoint M h
  disjoint N h
  disjoint R h
  disjoint U h
  disjoint .- h
  disjoint G h
  disjoint G x
  disjoint E h
  disjoint Z h
  disjoint Z x
  disjoint h w
  assert |- ( ph -> ( I ` <. Y , G , Z >. ) = E )

  proof
    wph
    cY
    cG
    cZ
    cotp
    cI
    cfv
    cE
    wceq
    cZ
    csn
    cN
    cfv
    #
    cM
    cfv
    cE
    csn
    cJ
    cfv
    wceq
    #
    cY
    cZ
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    cG
    cE
    cR
    co
    csn
    cJ
    cfv
    wceq
    wph
    @1
    cX
    cZ
    c.mi
    co
    csn
    cN
    cfv
    cM
    cfv
    cF
    cE
    cR
    co
    csn
    cJ
    cfv
    wceq
    #
    wph
    cX
    cF
    cZ
    cotp
    cI
    cfv
    #
    cE
    wceq
    @1
    @2
    wa
    mapdh.ee
    wph
    vx
    cC
    cD
    cQ
    cR
    cU
    vh
    cF
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
    cX
    cZ
    c.0
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    mapdh.k
    mapdhc.f
    mapdh.mn
    mapdhcl.x
    mapdhe.z
    wph
    @3
    cE
    cD
    mapdh.ee
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
    cZ
    c.0
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    mapdh.k
    mapdhc.f
    mapdh.mn
    mapdhcl.x
    wph
    cZ
    cV
    c.0
    csn
    #
    mapdhe.z
    eldifad
    #
    wph
    cX
    csn
    cN
    cfv
    #
    @0
    wne
    cY
    cX
    cZ
    cpr
    cN
    cfv
    wcel
    wn
    wph
    cN
    cV
    cU
    cY
    cZ
    c.0
    cX
    mapdh.v
    mapdhc.o
    mapdh.n
    wph
    cU
    cH
    cK
    cW
    mapdh.h
    mapdh.u
    mapdh.k
    dvhlvec
    #
    mapdhe4.y
    @5
    wph
    cX
    cV
    @4
    mapdhcl.x
    eldifad
    #
    mapdh.yz
    mapdh.xn
    lspindp1
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    @9
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
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    mapdh.k
    mapdhc.f
    mapdh.mn
    mapdhcl.x
    mapdhe4.y
    mapdhe.z
    mapdh.xn
    mapdh.yz
    mapdh.eg
    mapdh.ee
    mapdheq4lem
    wph
    vx
    cC
    cD
    cQ
    cR
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
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    mapdh.k
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
    mapdh.eg
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
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    mapdh.k
    mapdhc.f
    mapdh.mn
    mapdhcl.x
    wph
    cY
    cV
    @4
    mapdhe4.y
    eldifad
    #
    wph
    @6
    cY
    csn
    cN
    cfv
    #
    wne
    cZ
    cX
    cY
    cpr
    cN
    cfv
    wcel
    wn
    wph
    cN
    cV
    cU
    cY
    cZ
    c.0
    cX
    mapdh.v
    mapdhc.o
    mapdh.n
    @7
    @12
    mapdhe.z
    @8
    mapdh.yz
    mapdh.xn
    lspindp2
    simpld
    #
    mapdhcl
    eqeltrrd
    #
    wph
    @13
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
    @11
    cG
    wceq
    @16
    @17
    wa
    mapdh.eg
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
    mapdh.q
    mapdh.i
    mapdh.h
    mapdh.m
    mapdh.u
    mapdh.v
    mapdh.s
    mapdhc.o
    mapdh.n
    mapdh.c
    mapdh.d
    mapdh.r
    mapdh.j
    mapdh.k
    mapdhc.f
    mapdh.mn
    mapdhcl.x
    mapdhe4.y
    @15
    @14
    mapdheq
    mpbid
    simpld
    mapdhe4.y
    mapdhe.z
    @10
    mapdh.yz
    mapdheq
    mpbir2and
end
