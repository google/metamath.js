include "co.mm"
include "cfv.mm"
include "csn.mm"
include "wceq.mm"
include "cv.mm"
include "cdif.mm"
include "wreu.mm"
include "hdmap14lem1.mm"
include "eqcomd.mm"
include "cbs.mm"
include "c0g.mm"
include "eqid.mm"
include "lcdlvec.mm"
include "clmod.mm"
include "wcel.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "hdmapcl.mm"
include "hdmapnzcl.mm"
include "lspsneu.mm"
include "mpbid.mm"

theorem hdmap14lem3
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
  assert |- ( ph -> E! g e. ( A \ { Q } ) ( S ` ( F .x. X ) ) = ( g .xb ( S ` X ) ) )

  proof
    wph
    cF
    cX
    c.x
    co
    #
    cS
    cfv
    #
    csn
    cL
    cfv
    #
    cX
    cS
    cfv
    #
    csn
    cL
    cfv
    #
    wceq
    @1
    vg
    cv
    @3
    c.xb
    co
    wceq
    vg
    cA
    cQ
    csn
    cdif
    wreu
    wph
    @4
    @2
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
    hdmap14lem1
    eqcomd
    wph
    cP
    c.xb
    vg
    cA
    cL
    cQ
    cC
    cbs
    cfv
    #
    cC
    @1
    @3
    cC
    c0g
    cfv
    #
    @5
    eqid
    #
    hdmap14lem2.p
    hdmap14lem2.a
    hdmap14lem2.q
    hdmap14lem2.e
    @6
    eqid
    #
    hdmap14lem1.l
    wph
    cC
    cH
    cK
    cW
    hdmap14lem1.h
    hdmap14lem1.c
    hdmap14lem1.k
    lcdlvec
    wph
    cC
    @5
    cS
    @0
    cU
    cH
    cK
    cV
    cW
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.v
    hdmap14lem1.c
    @7
    hdmap14lem1.s
    hdmap14lem1.k
    wph
    cU
    clmod
    wcel
    cF
    cB
    wcel
    cX
    cV
    wcel
    @0
    cV
    wcel
    wph
    cU
    cH
    cK
    cW
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.k
    dvhlmod
    wph
    cF
    cB
    cZ
    csn
    hdmap14lem1.f
    eldifad
    wph
    cX
    cV
    c.0
    csn
    hdmap14lem3.x
    eldifad
    cF
    c.x
    cR
    cB
    cV
    cU
    cX
    hdmap14lem1.v
    hdmap14lem1.r
    hdmap14lem1.t
    hdmap14lem1.b
    lmodvscl
    syl3anc
    hdmapcl
    wph
    cC
    @5
    @6
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    c.0
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.v
    hdmap14lem3.o
    hdmap14lem1.c
    @8
    @7
    hdmap14lem1.s
    hdmap14lem1.k
    hdmap14lem3.x
    hdmapnzcl
    lspsneu
    mpbid
end
