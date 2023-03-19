include "csn.mm"
include "eldifad.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "eldifsni.mm"
include "syl.mm"
include "hdmap14lem1a.mm"

theorem hdmap14lem1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cF: class F
  let cH: class H
  let cK: class K
  let cL: class L
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  assume hdmap14lem1.h: |- H = ( LHyp ` K )
  assume hdmap14lem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmap14lem1.v: |- V = ( Base ` U )
  assume hdmap14lem1.t: |- .x. = ( .s ` U )
  assume hdmap14lem3.o: |- .0. = ( 0g ` U )
  assume hdmap14lem1.r: |- R = ( Scalar ` U )
  assume hdmap14lem1.b: |- B = ( Base ` R )
  assume hdmap14lem1.z: |- Z = ( 0g ` R )
  assume hdmap14lem1.c: |- C = ( ( LCDual ` K ) ` W )
  assume hdmap14lem2.e: |- .xb = ( .s ` C )
  assume hdmap14lem1.l: |- L = ( LSpan ` C )
  assume hdmap14lem2.p: |- P = ( Scalar ` C )
  assume hdmap14lem2.a: |- A = ( Base ` P )
  assume hdmap14lem2.q: |- Q = ( 0g ` P )
  assume hdmap14lem1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmap14lem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmap14lem3.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmap14lem1.f: |- ( ph -> F e. ( B \ { Z } ) )


  assert |- ( ph -> ( L ` { ( S ` X ) } ) = ( L ` { ( S ` ( F .x. X ) ) } ) )

  proof
    wph
    cA
    cB
    cC
    cP
    cR
    cS
    c.xb
    c.x
    cU
    cF
    cH
    cK
    cL
    cV
    cW
    cX
    cZ
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.v
    hdmap14lem1.t
    hdmap14lem1.r
    hdmap14lem1.b
    hdmap14lem1.c
    hdmap14lem2.e
    hdmap14lem1.l
    hdmap14lem2.p
    hdmap14lem2.a
    hdmap14lem1.s
    hdmap14lem1.k
    wph
    cX
    cV
    c.0
    csn
    hdmap14lem3.x
    eldifad
    wph
    cF
    cB
    cZ
    csn
    #
    hdmap14lem1.f
    eldifad
    hdmap14lem1.z
    wph
    cF
    cB
    @0
    cdif
    wcel
    cF
    cZ
    wne
    hdmap14lem1.f
    cF
    cB
    cZ
    eldifsni
    syl
    hdmap14lem1a
end
