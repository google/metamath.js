include "c0g.mm"
include "cfv.mm"
include "csg.mm"
include "eqid.mm"
include "hdmap1l6k.mm"

theorem hdmap1l6
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
  assume hdmap1-6.h: |- H = ( LHyp ` K )
  assume hdmap1-6.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap1-6.v: |- V = ( Base ` U )
  assume hdmap1-6.p: |- .+ = ( +g ` U )
  assume hdmap1-6.o: |- .0. = ( 0g ` U )
  assume hdmap1-6.n: |- N = ( LSpan ` U )
  assume hdmap1-6.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap1-6.d: |- D = ( Base ` C )
  assume hdmap1-6.a: |- .+b = ( +g ` C )
  assume hdmap1-6.l: |- L = ( LSpan ` C )
  assume hdmap1-6.m: |- M = ( ( mapd ` K ) ` W )
  assume hdmap1-6.i: |- I = ( ( HDMap1 ` K ) ` W )
  assume hdmap1-6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap1-6.f: |- ( ph -> F e. D )
  assume hdmap1-6.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap1-6.y: |- ( ph -> Y e. V )
  assume hdmap1-6.z: |- ( ph -> Z e. V )
  assume hdmap1-6.xn: |- ( ph -> -. X e. ( N ` { Y , Z } ) )
  assume hdmap1-6.mn: |- ( ph -> ( M ` ( N ` { X } ) ) = ( L ` { F } ) )


  assert |- ( ph -> ( I ` <. X , F , ( Y .+ Z ) >. ) = ( ( I ` <. X , F , Y >. ) .+b ( I ` <. X , F , Z >. ) ) )

  proof
    wph
    cC
    cD
    c.pl
    c.pb
    cC
    c0g
    cfv
    #
    cC
    csg
    cfv
    #
    cU
    cF
    cH
    cI
    cK
    cL
    cM
    cU
    csg
    cfv
    #
    cN
    cV
    cW
    cX
    cY
    c.0
    cZ
    hdmap1-6.h
    hdmap1-6.u
    hdmap1-6.v
    hdmap1-6.p
    @2
    eqid
    hdmap1-6.o
    hdmap1-6.n
    hdmap1-6.c
    hdmap1-6.d
    hdmap1-6.a
    @1
    eqid
    @0
    eqid
    hdmap1-6.l
    hdmap1-6.m
    hdmap1-6.i
    hdmap1-6.k
    hdmap1-6.f
    hdmap1-6.x
    hdmap1-6.mn
    hdmap1-6.y
    hdmap1-6.z
    hdmap1-6.xn
    hdmap1l6k
end
