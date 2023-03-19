include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "crn.mm"
include "wcel.mm"
include "csn.mm"
include "cfv.mm"
include "wss.mm"
include "hgmaprnlem2N.mm"
include "dvhlmod.mm"
include "eldifad.mm"
include "lspsnss2.mm"
include "mpbid.mm"
include "w3a.mm"
include "chlt.mm"
include "wa.mm"
include "3ad2ant1.mm"
include "cdif.mm"
include "simp2.mm"
include "simp3.mm"
include "hgmaprnlem1N.mm"
include "rexlimdv3a.mm"
include "mpd.mm"

theorem hgmaprnlem3N
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
  let vk: setvar k
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

  disjoint s t
  disjoint s z
  disjoint t z
  disjoint B k
  disjoint G k
  disjoint N k
  disjoint R k
  disjoint .x. k
  disjoint U k
  disjoint V k
  disjoint k ph
  disjoint k s
  disjoint k t
  disjoint k z
  assert |- ( ph -> z e. ran G )

  proof
    wph
    vs
    cv
    #
    vk
    cv
    #
    vt
    cv
    #
    c.x
    co
    wceq
    #
    vk
    cB
    wrex
    #
    vz
    cv
    #
    cG
    crn
    wcel
    #
    wph
    @0
    csn
    cN
    cfv
    @2
    csn
    cN
    cfv
    wss
    @4
    wph
    vz
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    c.xb
    c.x
    cU
    cG
    cH
    cK
    cL
    cM
    cN
    cV
    cW
    c.0
    vs
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.r
    hgmaprnlem1.b
    hgmaprnlem1.t
    hgmaprnlem1.o
    hgmaprnlem1.c
    hgmaprnlem1.d
    hgmaprnlem1.p
    hgmaprnlem1.a
    hgmaprnlem1.e
    hgmaprnlem1.q
    hgmaprnlem1.s
    hgmaprnlem1.g
    hgmaprnlem1.k
    hgmaprnlem1.z
    hgmaprnlem1.t2
    hgmaprnlem1.s2
    hgmaprnlem1.sz
    hgmaprnlem1.m
    hgmaprnlem1.n
    hgmaprnlem1.l
    hgmaprnlem2N
    wph
    cR
    c.x
    vk
    cB
    cN
    cV
    cU
    @0
    @2
    hgmaprnlem1.v
    hgmaprnlem1.r
    hgmaprnlem1.b
    hgmaprnlem1.t
    hgmaprnlem1.n
    wph
    cU
    cH
    cK
    cW
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.k
    dvhlmod
    hgmaprnlem1.s2
    wph
    @2
    cV
    c.0
    csn
    #
    hgmaprnlem1.t2
    eldifad
    lspsnss2
    mpbid
    wph
    @3
    @6
    vk
    cB
    wph
    @1
    cB
    wcel
    #
    @3
    w3a
    vz
    vt
    cA
    cB
    cC
    cD
    cP
    cQ
    cR
    cS
    c.xb
    c.x
    cU
    vk
    cG
    cH
    cK
    cV
    cW
    c.0
    vs
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.r
    hgmaprnlem1.b
    hgmaprnlem1.t
    hgmaprnlem1.o
    hgmaprnlem1.c
    hgmaprnlem1.d
    hgmaprnlem1.p
    hgmaprnlem1.a
    hgmaprnlem1.e
    hgmaprnlem1.q
    hgmaprnlem1.s
    hgmaprnlem1.g
    wph
    @8
    cK
    chlt
    wcel
    cW
    cH
    wcel
    wa
    @3
    hgmaprnlem1.k
    3ad2ant1
    wph
    @8
    @5
    cA
    wcel
    @3
    hgmaprnlem1.z
    3ad2ant1
    wph
    @8
    @2
    cV
    @7
    cdif
    wcel
    @3
    hgmaprnlem1.t2
    3ad2ant1
    wph
    @8
    @0
    cV
    wcel
    @3
    hgmaprnlem1.s2
    3ad2ant1
    wph
    @8
    @0
    cS
    cfv
    @5
    @2
    cS
    cfv
    c.xb
    co
    wceq
    @3
    hgmaprnlem1.sz
    3ad2ant1
    wph
    @8
    @3
    simp2
    wph
    @8
    @3
    simp3
    hgmaprnlem1N
    rexlimdv3a
    mpd
end
