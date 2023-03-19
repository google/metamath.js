include "mapdh6kN.mm"

theorem mapdh6N
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vh: setvar h
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
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume mapdh6.h: |- H = ( LHyp ` K )
  assume mapdh6.u: |- U = ( ( DVecH ` K ) ` W )
  assume mapdh6.v: |- V = ( Base ` U )
  assume mapdh6.p: |- .+ = ( +g ` U )
  assume mapdh6.s: |- .- = ( -g ` U )
  assume mapdh6.o: |- .0. = ( 0g ` U )
  assume mapdh6.n: |- N = ( LSpan ` U )
  assume mapdh6.c: |- C = ( ( LCDual ` K ) ` W )
  assume mapdh6.d: |- D = ( Base ` C )
  assume mapdh6.a: |- .+b = ( +g ` C )
  assume mapdh6.r: |- R = ( -g ` C )
  assume mapdh6.q: |- Q = ( 0g ` C )
  assume mapdh6.j: |- J = ( LSpan ` C )
  assume mapdh6.m: |- M = ( ( mapd ` K ) ` W )
  assume mapdh6.i: |- I = ( x e. _V |-> if ( ( 2nd ` x ) = .0. , Q , ( iota_ h e. D ( ( M ` ( N ` { ( 2nd ` x ) } ) ) = ( J ` { h } ) /\ ( M ` ( N ` { ( ( 1st ` ( 1st ` x ) ) .- ( 2nd ` x ) ) } ) ) = ( J ` { ( ( 2nd ` ( 1st ` x ) ) R h ) } ) ) ) ) )
  assume mapdh6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume mapdh6.f: |- ( ph -> F e. D )
  assume mapdh6.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume mapdh6.y: |- ( ph -> Y e. V )
  assume mapdh6.z: |- ( ph -> Z e. V )
  assume mapdh6.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume mapdh6.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( J ` { F } ) )

  disjoint h x
  disjoint .- h
  disjoint .- x
  disjoint .+b h
  disjoint C h
  disjoint D h
  disjoint D x
  disjoint F h
  disjoint F x
  disjoint I h
  disjoint I x
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
  disjoint .+ h
  disjoint .+ x
  disjoint R h
  disjoint R x
  disjoint U h
  disjoint X h
  disjoint X x
  disjoint Y h
  disjoint Y x
  disjoint Z h
  disjoint Z x
  disjoint V h
  assert |- ( ph -> ( I ` <. X , F , ( Y .+ Z ) >. ) = ( ( I ` <. X , F , Y >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    vx
    cC
    cD
    c.pl
    c.pb
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
    cZ
    mapdh6.q
    mapdh6.i
    mapdh6.h
    mapdh6.m
    mapdh6.u
    mapdh6.v
    mapdh6.s
    mapdh6.o
    mapdh6.n
    mapdh6.c
    mapdh6.d
    mapdh6.r
    mapdh6.j
    mapdh6.k
    mapdh6.f
    mapdh6.mn
    mapdh6.x
    mapdh6.p
    mapdh6.a
    mapdh6.y
    mapdh6.z
    mapdh6.xn
    mapdh6kN
end
