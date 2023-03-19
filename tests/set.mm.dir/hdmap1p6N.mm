include "hdmap1l6.mm"

theorem hdmap1p6N
  let wph: wff ph
  let cC: class C
  let cD: class D
  let c.pl: class .+
  let c.pb: class .+b
  let cU: class U
  let cF: class F
  let cH: class H
  let cI: class I
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  assume hdmap1p6.h: |- H = ( LHyp ` K )
  assume hdmap1p6.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1p6.v: |- V = ( Base ` U )
  assume hdmap1p6.p: |- .+ = ( +g ` U )
  assume hdmap1p6.o: |- .0. = ( 0g ` U )
  assume hdmap1p6.n: |- N = ( LSpan ` U )
  assume hdmap1p6.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1p6.d: |- D = ( Base ` C )
  assume hdmap1p6.a: |- .+b = ( +g ` C )
  assume hdmap1p6.l: |- L = ( LSpan ` C )
  assume hdmap1p6.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1p6.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1p6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1p6.f: |- ( ph -> F e. D )
  assume hdmap1p6.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1p6.y: |- ( ph -> Y e. V )
  assume hdmap1p6.z: |- ( ph -> Z e. V )
  assume hdmap1p6.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume hdmap1p6.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )


  assert |- ( ph -> ( I ` <. X , F , ( Y .+ Z ) >. ) = ( ( I ` <. X , F , Y >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    cC
    cD
    c.pl
    c.pb
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    hdmap1p6.h
    hdmap1p6.u
    hdmap1p6.v
    hdmap1p6.p
    hdmap1p6.o
    hdmap1p6.n
    hdmap1p6.c
    hdmap1p6.d
    hdmap1p6.a
    hdmap1p6.l
    hdmap1p6.m
    hdmap1p6.i
    hdmap1p6.k
    hdmap1p6.f
    hdmap1p6.x
    hdmap1p6.y
    hdmap1p6.z
    hdmap1p6.xn
    hdmap1p6.mn
    hdmap1l6
end
