include "cv.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "co.mm"
include "clmod.mm"
include "wcel.mm"
include "lcdlmod.mm"
include "eldifad.mm"
include "hdmapcl.mm"
include "lspsnvsi.mm"
include "syl3anc.mm"
include "hdmap10.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "3sstr4d.mm"
include "clss.mm"
include "eqid.mm"
include "dvhlmod.mm"
include "lspsncl.mm"
include "syl2anc.mm"
include "mapdord.mm"
include "mpbid.mm"

theorem hgmaprnlem2N
  let wph: wff ph
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cS: class S
  let c.xb: class .xb
  let c.x: class .x.
  let cU: class U
  let cG: class G
  let cH: class H
  let cK: class K
  let cL: class L
  let cM: class M
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vs: setvar s
  assume hgmaprnlem1.h: |- H = ( LHyp ` K )
  assume hgmaprnlem1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hgmaprnlem1.v: |- V = ( Base ` U )
  assume hgmaprnlem1.r: |- R = ( Scalar ` U )
  assume hgmaprnlem1.b: |- B = ( Base ` R )
  assume hgmaprnlem1.t: |- .x. = ( .s ` U )
  assume hgmaprnlem1.o: |- .0. = ( 0g ` U )
  assume hgmaprnlem1.c: |- C = ( ( LCDual ` K ) ` W )
  assume hgmaprnlem1.d: |- D = ( Base ` C )
  assume hgmaprnlem1.p: |- P = ( Scalar ` C )
  assume hgmaprnlem1.a: |- A = ( Base ` P )
  assume hgmaprnlem1.e: |- .xb = ( .s ` C )
  assume hgmaprnlem1.q: |- Q = ( 0g ` C )
  assume hgmaprnlem1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hgmaprnlem1.g: |- G = ( ( HGMap ` K ) ` W )
  assume hgmaprnlem1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hgmaprnlem1.z: |- ( ph -> z e. A )
  assume hgmaprnlem1.t2: |- ( ph -> t e. ( V \ { .0. } ) )
  assume hgmaprnlem1.s2: |- ( ph -> s e. V )
  assume hgmaprnlem1.sz: |- ( ph -> ( S ` s ) = ( z .xb ( S ` t ) ) )
  assume hgmaprnlem1.m: |- M = ( ( mapd ` K ) ` W )
  assume hgmaprnlem1.n: |- N = ( LSpan ` U )
  assume hgmaprnlem1.l: |- L = ( LSpan ` C )


  assert |- ( ph -> ( N ` { s } ) C_ ( N ` { t } ) )

  proof
    wph
    vs
    cv
    #
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    vt
    cv
    #
    csn
    cN
    cfv
    #
    cM
    cfv
    #
    wss
    @1
    @4
    wss
    wph
    vz
    cv
    #
    @3
    cS
    cfv
    #
    c.xb
    co
    #
    csn
    #
    cL
    cfv
    #
    @7
    csn
    cL
    cfv
    #
    @2
    @5
    wph
    cC
    clmod
    wcel
    @6
    cA
    wcel
    @7
    cD
    wcel
    @10
    @11
    wss
    wph
    cC
    cH
    cK
    cW
    hgmaprnlem1.h
    hgmaprnlem1.c
    hgmaprnlem1.k
    lcdlmod
    hgmaprnlem1.z
    wph
    cC
    cD
    cS
    @3
    cU
    cH
    cK
    cV
    cW
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.c
    hgmaprnlem1.d
    hgmaprnlem1.s
    hgmaprnlem1.k
    wph
    @3
    cV
    c.0
    csn
    hgmaprnlem1.t2
    eldifad
    #
    hdmapcl
    @6
    c.xb
    cP
    cA
    cL
    cD
    cC
    @7
    hgmaprnlem1.p
    hgmaprnlem1.a
    hgmaprnlem1.d
    hgmaprnlem1.e
    hgmaprnlem1.l
    lspsnvsi
    syl3anc
    wph
    @2
    @0
    cS
    cfv
    #
    csn
    #
    cL
    cfv
    @10
    wph
    cC
    cS
    @0
    cU
    cH
    cK
    cL
    cM
    cN
    cV
    cW
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.n
    hgmaprnlem1.c
    hgmaprnlem1.l
    hgmaprnlem1.m
    hgmaprnlem1.s
    hgmaprnlem1.k
    hgmaprnlem1.s2
    hdmap10
    wph
    @14
    @9
    cL
    wph
    @13
    @8
    hgmaprnlem1.sz
    sneqd
    fveq2d
    eqtrd
    wph
    cC
    cS
    @3
    cU
    cH
    cK
    cL
    cM
    cN
    cV
    cW
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.n
    hgmaprnlem1.c
    hgmaprnlem1.l
    hgmaprnlem1.m
    hgmaprnlem1.s
    hgmaprnlem1.k
    @12
    hdmap10
    3sstr4d
    wph
    cU
    clss
    cfv
    #
    cU
    cH
    cK
    cM
    cW
    @1
    @4
    hgmaprnlem1.h
    hgmaprnlem1.u
    @15
    eqid
    #
    hgmaprnlem1.m
    hgmaprnlem1.k
    wph
    cU
    clmod
    wcel
    #
    @0
    cV
    wcel
    @1
    @15
    wcel
    wph
    cU
    cH
    cK
    cW
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.k
    dvhlmod
    #
    hgmaprnlem1.s2
    @15
    cN
    cV
    cU
    @0
    hgmaprnlem1.v
    @16
    hgmaprnlem1.n
    lspsncl
    syl2anc
    wph
    @17
    @3
    cV
    wcel
    @4
    @15
    wcel
    @18
    @12
    @15
    cN
    cV
    cU
    @3
    hgmaprnlem1.v
    @16
    hgmaprnlem1.n
    lspsncl
    syl2anc
    mapdord
    mpbid
end
