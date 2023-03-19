include "cv.mm"
include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "eldifad.mm"
include "wne.mm"
include "dvhlvec.mm"
include "lspindpi.mm"
include "simpld.mm"
include "necomd.mm"
include "mapdhcl.mm"
include "eqeltrrd.mm"
include "mapdheq2.mm"
include "mpd.mm"

theorem mapdh7eN
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
  let cG: class G
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
  assume mapdh7b: |- ( ph -> ( I ` <. u , F , w >. ) = E )

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
  disjoint G h
  disjoint G x
  assert |- ( ph -> ( I ` <. w , E , u >. ) = F )

  proof
    wph
    vu
    cv
    #
    cF
    vw
    cv
    #
    cotp
    cI
    cfv
    #
    cE
    wceq
    @1
    cE
    @0
    cotp
    cI
    cfv
    cF
    wceq
    mapdh7b
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
    mapdh7.f
    mapdh7.mn
    mapdh7.x
    mapdh7.z
    wph
    @2
    cE
    cD
    mapdh7b
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
    mapdh7.f
    mapdh7.mn
    mapdh7.x
    wph
    @1
    cV
    c.0
    csn
    #
    mapdh7.z
    eldifad
    #
    wph
    @1
    csn
    cN
    cfv
    #
    @0
    csn
    cN
    cfv
    #
    wph
    @5
    @6
    wne
    @5
    vv
    cv
    #
    csn
    cN
    cfv
    wne
    wph
    cN
    cV
    cU
    @1
    @0
    @7
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
    @4
    wph
    @0
    cV
    @3
    mapdh7.x
    eldifad
    wph
    @7
    cV
    @3
    mapdh7.y
    eldifad
    mapdh7.wn
    lspindpi
    simpld
    necomd
    #
    mapdhcl
    eqeltrrd
    @8
    mapdheq2
    mpd
end
