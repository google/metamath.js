include "co.mm"
include "cfv.mm"
include "cv.mm"
include "wceq.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "wreu.mm"
include "wrex.mm"
include "wn.mm"
include "wb.mm"
include "wcel.mm"
include "wa.mm"
include "c0g.mm"
include "wne.mm"
include "cbs.mm"
include "eqid.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lmodvscl.mm"
include "syl3anc.mm"
include "eldifsni.mm"
include "syl.mm"
include "dvhlvec.mm"
include "lvecvsn0.mm"
include "mpbir2and.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "hdmapnzcl.mm"
include "adantr.mm"
include "elsni.mm"
include "oveq1d.mm"
include "lcdlmod.mm"
include "hdmapcl.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "sylan9eqr.mm"
include "neeqtrrd.mm"
include "neneqd.mm"
include "nrexdv.mm"
include "reuun2.mm"
include "lmod0cl.mm"
include "difsnid.mm"
include "reueq1.mm"
include "4syl.mm"
include "bitr3d.mm"

theorem hdmap14lem4a
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
  assert |- ( ph -> ( E! g e. ( A \ { Q } ) ( S ` ( F .x. X ) ) = ( g .xb ( S ` X ) ) <-> E! g e. A ( S ` ( F .x. X ) ) = ( g .xb ( S ` X ) ) ) )

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
    vg
    cv
    #
    cX
    cS
    cfv
    #
    c.xb
    co
    #
    wceq
    #
    vg
    cA
    cQ
    csn
    #
    cdif
    #
    @6
    cun
    #
    wreu
    #
    @5
    vg
    @7
    wreu
    #
    @5
    vg
    cA
    wreu
    #
    wph
    @5
    vg
    @6
    wrex
    wn
    @9
    @10
    wb
    wph
    @5
    vg
    @6
    wph
    @2
    @6
    wcel
    #
    wa
    #
    @1
    @4
    @13
    @1
    cC
    c0g
    cfv
    #
    @4
    wph
    @1
    @14
    wne
    #
    @12
    wph
    @1
    cC
    cbs
    cfv
    #
    @14
    csn
    cdif
    wcel
    @15
    wph
    cC
    @16
    @14
    cS
    @0
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
    @14
    eqid
    #
    @16
    eqid
    #
    hdmap14lem1.s
    hdmap14lem1.k
    wph
    @0
    cV
    wcel
    #
    @0
    c.0
    wne
    #
    @0
    cV
    c.0
    csn
    #
    cdif
    #
    wcel
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
    @19
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
    #
    hdmap14lem1.f
    eldifad
    #
    wph
    cX
    cV
    @21
    hdmap14lem3.x
    eldifad
    #
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
    wph
    @20
    cF
    cZ
    wne
    #
    cX
    c.0
    wne
    #
    wph
    cF
    cB
    @23
    cdif
    wcel
    @26
    hdmap14lem1.f
    cF
    cB
    cZ
    eldifsni
    syl
    wph
    cX
    @22
    wcel
    @27
    hdmap14lem3.x
    cX
    cV
    c.0
    eldifsni
    syl
    wph
    cF
    c.x
    cR
    cB
    cZ
    cV
    cU
    cX
    c.0
    hdmap14lem1.v
    hdmap14lem1.t
    hdmap14lem1.r
    hdmap14lem1.b
    hdmap14lem1.z
    hdmap14lem3.o
    wph
    cU
    cH
    cK
    cW
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.k
    dvhlvec
    @24
    @25
    lvecvsn0
    mpbir2and
    @0
    cV
    c.0
    eldifsn
    sylanbrc
    hdmapnzcl
    @1
    @16
    @14
    eldifsni
    syl
    adantr
    @12
    wph
    @4
    cQ
    @3
    c.xb
    co
    #
    @14
    @12
    @2
    cQ
    @3
    c.xb
    @2
    cQ
    elsni
    oveq1d
    wph
    cC
    clmod
    wcel
    #
    @3
    @16
    wcel
    @28
    @14
    wceq
    wph
    cC
    cH
    cK
    cW
    hdmap14lem1.h
    hdmap14lem1.c
    hdmap14lem1.k
    lcdlmod
    #
    wph
    cC
    @16
    cS
    cX
    cU
    cH
    cK
    cV
    cW
    hdmap14lem1.h
    hdmap14lem1.u
    hdmap14lem1.v
    hdmap14lem1.c
    @18
    hdmap14lem1.s
    hdmap14lem1.k
    @25
    hdmapcl
    c.xb
    cP
    cQ
    @16
    cC
    @3
    @14
    @18
    hdmap14lem2.p
    hdmap14lem2.e
    hdmap14lem2.q
    @17
    lmod0vs
    syl2anc
    sylan9eqr
    neeqtrrd
    neneqd
    nrexdv
    @5
    vg
    @7
    @6
    reuun2
    syl
    wph
    @29
    cQ
    cA
    wcel
    @8
    cA
    wceq
    @9
    @11
    wb
    @30
    cP
    cA
    cC
    cQ
    hdmap14lem2.p
    hdmap14lem2.a
    hdmap14lem2.q
    lmod0cl
    cA
    cQ
    difsnid
    @5
    vg
    @8
    cA
    reueq1
    4syl
    bitr3d
end
