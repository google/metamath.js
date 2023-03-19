include "cv.mm"
include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "mapdh7dN.mm"
include "csn.mm"
include "eldifad.mm"
include "mapdhcl.mm"
include "eqeltrrd.mm"
include "co.mm"
include "wa.mm"
include "mapdheq.mm"
include "mpbid.mm"
include "simpld.mm"
include "wne.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "necomd.mm"
include "simprd.mm"
include "mapdheq2.mm"
include "mpd.mm"

theorem mapdh7fN
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
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
  let c.0: class .0.
  assume mapdh7.h: |- H = ( LHyp ` K )
  assume mapdh7.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh7.v: |- V = ( Base ` U )
  assume mapdh7.s: |- .- = ( -g ` U )
  assume mapdh7.o: |- .0. = ( 0g ` U )
  assume mapdh7.n: |- N = ( LSpan ` U )
  assume mapdh7.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh7.d: |- D = ( Base ` C )
  assume mapdh7.r: |- R = ( -g ` C )
  assume mapdh7.q: |- Q = ( 0g ` C )
  assume mapdh7.j: |- J = ( LSpan ` C )
  assume mapdh7.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh7.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh7.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdh7.f: |- ( ph -> F e. D )
  assume mapdh7.mn: |- ( ph -> ( M ` ( N ` { u } ) ) = ( J ` { F } ) )
  assume mapdh7.x: |- ( ph -> u e. ( V \ { .0. } ) )
  assume mapdh7.y: |- ( ph -> v e. ( V \ { .0. } ) )
  assume mapdh7.z: |- ( ph -> w e. ( V \ { .0. } ) )
  assume mapdh7.ne: |- ( ph -> ( N ` { u } ) =/= ( N ` { v } ) )
  assume mapdh7.wn: |- ( ph -> -. w e. ( N ` { u , v } ) )
  assume mapdh7a: |- ( ph -> ( I ` <. u , F , v >. ) = G )
  assume mapdh7.b: |- ( ph -> ( I ` <. u , F , w >. ) = E )

  disjoint h x
  disjoint .- h
  disjoint .- x
  disjoint C h
  disjoint D h
  disjoint D x
  disjoint E h
  disjoint E x
  disjoint F h
  disjoint F x
  disjoint G h
  disjoint G x
  disjoint .0. h
  disjoint .0. x
  disjoint J h
  disjoint J x
  disjoint M h
  disjoint M x
  disjoint N h
  disjoint N x
  disjoint h ph
  disjoint Q x
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint v w
  disjoint v x
  disjoint w x
  disjoint R h
  disjoint R x
  disjoint U h
  assert |- ( ph -> ( I ` <. w , E , v >. ) = G )

  proof
    wph
    vv
    cv
    #
    cG
    vw
    cv
    #
    cotp
    cI
    cfv
    cE
    wceq
    @1
    cE
    @0
    cotp
    cI
    cfv
    cG
    wceq
    wph
    vx
    vw
    vv
    vu
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
    c.0
    mapdh7.h
    mapdh7.u
    mapdh7.v
    mapdh7.s
    mapdh7.o
    mapdh7.n
    mapdh7.c
    mapdh7.d
    mapdh7.r
    mapdh7.q
    mapdh7.j
    mapdh7.m
    mapdh7.i
    mapdh7.k
    mapdh7.f
    mapdh7.mn
    mapdh7.x
    mapdh7.y
    mapdh7.z
    mapdh7.ne
    mapdh7.wn
    mapdh7a
    mapdh7.b
    mapdh7dN
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
    @0
    @1
    c.0
    mapdh7.q
    mapdh7.i
    mapdh7.h
    mapdh7.m
    mapdh7.u
    mapdh7.v
    mapdh7.s
    mapdh7.o
    mapdh7.n
    mapdh7.c
    mapdh7.d
    mapdh7.r
    mapdh7.j
    mapdh7.k
    wph
    vu
    cv
    #
    cF
    @0
    cotp
    cI
    cfv
    #
    cG
    cD
    mapdh7a
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
    @2
    @0
    c.0
    mapdh7.q
    mapdh7.i
    mapdh7.h
    mapdh7.m
    mapdh7.u
    mapdh7.v
    mapdh7.s
    mapdh7.o
    mapdh7.n
    mapdh7.c
    mapdh7.d
    mapdh7.r
    mapdh7.j
    mapdh7.k
    mapdh7.f
    mapdh7.mn
    mapdh7.x
    wph
    @0
    cV
    c.0
    csn
    #
    mapdh7.y
    eldifad
    #
    mapdh7.ne
    mapdhcl
    eqeltrrd
    #
    wph
    @0
    csn
    cN
    cfv
    #
    cM
    cfv
    cG
    csn
    cJ
    cfv
    wceq
    #
    @2
    @0
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
    @3
    cG
    wceq
    @8
    @9
    wa
    mapdh7a
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
    @2
    @0
    c.0
    mapdh7.q
    mapdh7.i
    mapdh7.h
    mapdh7.m
    mapdh7.u
    mapdh7.v
    mapdh7.s
    mapdh7.o
    mapdh7.n
    mapdh7.c
    mapdh7.d
    mapdh7.r
    mapdh7.j
    mapdh7.k
    mapdh7.f
    mapdh7.mn
    mapdh7.x
    mapdh7.y
    @6
    mapdh7.ne
    mapdheq
    mpbid
    simpld
    mapdh7.y
    mapdh7.z
    wph
    @2
    cF
    @1
    cotp
    cI
    cfv
    cE
    cD
    mapdh7.b
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
    @2
    @1
    c.0
    mapdh7.q
    mapdh7.i
    mapdh7.h
    mapdh7.m
    mapdh7.u
    mapdh7.v
    mapdh7.s
    mapdh7.o
    mapdh7.n
    mapdh7.c
    mapdh7.d
    mapdh7.r
    mapdh7.j
    mapdh7.k
    mapdh7.f
    mapdh7.mn
    mapdh7.x
    wph
    @1
    cV
    @4
    mapdh7.z
    eldifad
    #
    wph
    @1
    csn
    cN
    cfv
    #
    @2
    csn
    cN
    cfv
    #
    wph
    @11
    @12
    wne
    #
    @11
    @7
    wne
    #
    wph
    cN
    cV
    cU
    @1
    @2
    @0
    mapdh7.v
    mapdh7.n
    wph
    cU
    cH
    cK
    cW
    mapdh7.h
    mapdh7.u
    mapdh7.k
    dvhlvec
    @10
    wph
    @2
    cV
    @4
    mapdh7.x
    eldifad
    @5
    mapdh7.wn
    lspindpi
    #
    simpld
    necomd
    mapdhcl
    eqeltrrd
    wph
    @11
    @7
    wph
    @13
    @14
    @15
    simprd
    necomd
    mapdheq2
    mpd
end
