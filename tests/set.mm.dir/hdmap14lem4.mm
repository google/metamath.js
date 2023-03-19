include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "wreu.mm"
include "hdmap14lem3.mm"
include "hdmap14lem4a.mm"
include "mpbid.mm"

theorem hdmap14lem4
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
  let vg: setvar g
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

  disjoint A g
  disjoint .xb g
  disjoint F g
  disjoint Q g
  disjoint S g
  disjoint .x. g
  disjoint X g
  disjoint g ph
  assert |- ( ph -> E! g e. A ( S ` ( F .x. X ) ) = ( g .xb ( S ` X ) ) )

  proof
    wph
    cF
    cX
    c.x
    co
    cS
    cfv
    vg
    cv
    cX
    cS
    cfv
    c.xb
    co
    wceq
    #
    vg
    cA
    cQ
    csn
    cdif
    wreu
    @0
    vg
    cA
    wreu
    wph
    cA
    cB
    cC
    cP
    cQ
    cR
    cS
    c.xb
    c.x
    cU
    vg
    cF
    cH
    cK
    cL
    cV
    cW
    cX
    c.0
    cZ
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.v
    hdmap14lem1.t
    hdmap14lem3.o
    hdmap14lem1.r
    hdmap14lem1.b
    hdmap14lem1.z
    hdmap14lem1.c
    hdmap14lem2.e
    hdmap14lem1.l
    hdmap14lem2.p
    hdmap14lem2.a
    hdmap14lem2.q
    hdmap14lem1.s
    hdmap14lem1.k
    hdmap14lem3.x
    hdmap14lem1.f
    hdmap14lem3
    wph
    cA
    cB
    cC
    cP
    cQ
    cR
    cS
    c.xb
    c.x
    cU
    vg
    cF
    cH
    cK
    cL
    cV
    cW
    cX
    c.0
    cZ
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.v
    hdmap14lem1.t
    hdmap14lem3.o
    hdmap14lem1.r
    hdmap14lem1.b
    hdmap14lem1.z
    hdmap14lem1.c
    hdmap14lem2.e
    hdmap14lem1.l
    hdmap14lem2.p
    hdmap14lem2.a
    hdmap14lem2.q
    hdmap14lem1.s
    hdmap14lem1.k
    hdmap14lem3.x
    hdmap14lem1.f
    hdmap14lem4a
    mpbid
end
