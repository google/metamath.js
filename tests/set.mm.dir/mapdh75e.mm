include "cotp.mm"
include "cfv.mm"
include "wceq.mm"
include "csn.mm"
include "eldifad.mm"
include "mapdhcl.mm"
include "eqeltrrd.mm"
include "mapdheq2.mm"
include "mpd.mm"

theorem mapdh75e
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
  let c.0: class .0.
  let cZ: class Z
  let cG: class G
  let cY: class Y
  assume mapdh75.h: |- H = ( LHyp ` K )
  assume mapdh75.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh75.v: |- V = ( Base ` U )
  assume mapdh75.s: |- .- = ( -g ` U )
  assume mapdh75.o: |- .0. = ( 0g ` U )
  assume mapdh75.n: |- N = ( LSpan ` U )
  assume mapdh75.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh75.d: |- D = ( Base ` C )
  assume mapdh75.r: |- R = ( -g ` C )
  assume mapdh75.q: |- Q = ( 0g ` C )
  assume mapdh75.j: |- J = ( LSpan ` C )
  assume mapdh75.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh75.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh75.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdh75.f: |- ( ph -> F e. D )
  assume mapdh75.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )
  assume mapdh75b: |- ( ph -> ( I ` <. X , F , Z >. ) = E )
  assume mapdh75e.ne: |- ( ph -> ( N ` { X } ) =/= ( N ` { Z } ) )
  assume mapdh75e.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh75e.z: |- ( ph -> Z e. ( V \ { .0. } ) )

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
  disjoint R h
  disjoint R x
  disjoint U h
  disjoint X h
  disjoint X x
  disjoint Z h
  disjoint Z x
  disjoint G h
  disjoint G x
  disjoint Y h
  disjoint Y x
  assert |- ( ph -> ( I ` <. Z , E , X >. ) = F )

  proof
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
    cZ
    cE
    cX
    cotp
    cI
    cfv
    cF
    wceq
    mapdh75b
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
    mapdh75.q
    mapdh75.i
    mapdh75.h
    mapdh75.m
    mapdh75.u
    mapdh75.v
    mapdh75.s
    mapdh75.o
    mapdh75.n
    mapdh75.c
    mapdh75.d
    mapdh75.r
    mapdh75.j
    mapdh75.k
    mapdh75.f
    mapdh75.mn
    mapdh75e.x
    mapdh75e.z
    wph
    @0
    cE
    cD
    mapdh75b
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
    mapdh75.q
    mapdh75.i
    mapdh75.h
    mapdh75.m
    mapdh75.u
    mapdh75.v
    mapdh75.s
    mapdh75.o
    mapdh75.n
    mapdh75.c
    mapdh75.d
    mapdh75.r
    mapdh75.j
    mapdh75.k
    mapdh75.f
    mapdh75.mn
    mapdh75e.x
    wph
    cZ
    cV
    c.0
    csn
    mapdh75e.z
    eldifad
    mapdh75e.ne
    mapdhcl
    eqeltrrd
    mapdh75e.ne
    mapdheq2
    mpd
end
