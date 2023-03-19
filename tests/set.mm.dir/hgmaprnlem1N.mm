include "cv.mm"
include "cfv.mm"
include "crn.mm"
include "co.mm"
include "wceq.mm"
include "fveq2d.mm"
include "csn.mm"
include "eldifad.mm"
include "hgmapvs.mm"
include "3eqtr3d.mm"
include "lcdlvec.mm"
include "hgmapdcl.mm"
include "hdmapcl.mm"
include "wne.mm"
include "cdif.mm"
include "wcel.mm"
include "eldifsni.mm"
include "syl.mm"
include "hdmapeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "lvecvscan2.mm"
include "mpbid.mm"
include "wfn.mm"
include "hgmapfnN.mm"
include "fnfvelrn.mm"
include "syl2anc.mm"
include "eqeltrd.mm"

theorem hgmaprnlem1N
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
  let vk: setvar k
  let cG: class G
  let cH: class H
  let cK: class K
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
  assume hgmaprnlem1.k2: |- ( ph -> k e. B )
  assume hgmaprnlem1.sk: |- ( ph -> s = ( k .x. t ) )


  assert |- ( ph -> z e. ran G )

  proof
    wph
    vz
    cv
    #
    vk
    cv
    #
    cG
    cfv
    #
    cG
    crn
    #
    wph
    @0
    vt
    cv
    #
    cS
    cfv
    #
    c.xb
    co
    #
    @2
    @5
    c.xb
    co
    #
    wceq
    @0
    @2
    wceq
    wph
    vs
    cv
    #
    cS
    cfv
    @1
    @4
    c.x
    co
    #
    cS
    cfv
    @6
    @7
    wph
    @8
    @9
    cS
    hgmaprnlem1.sk
    fveq2d
    hgmaprnlem1.sz
    wph
    cB
    cC
    cR
    cS
    c.xb
    c.x
    cU
    @1
    cG
    cH
    cK
    cV
    cW
    @4
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.t
    hgmaprnlem1.r
    hgmaprnlem1.b
    hgmaprnlem1.c
    hgmaprnlem1.e
    hgmaprnlem1.s
    hgmaprnlem1.g
    hgmaprnlem1.k
    wph
    @4
    cV
    c.0
    csn
    #
    hgmaprnlem1.t2
    eldifad
    #
    hgmaprnlem1.k2
    hgmapvs
    3eqtr3d
    wph
    @0
    @2
    c.xb
    cP
    cA
    cD
    cC
    @5
    cQ
    hgmaprnlem1.d
    hgmaprnlem1.e
    hgmaprnlem1.p
    hgmaprnlem1.a
    hgmaprnlem1.q
    wph
    cC
    cH
    cK
    cW
    hgmaprnlem1.h
    hgmaprnlem1.c
    hgmaprnlem1.k
    lcdlvec
    hgmaprnlem1.z
    wph
    cA
    cB
    cC
    cP
    cR
    cU
    @1
    cG
    cH
    cK
    cW
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.r
    hgmaprnlem1.b
    hgmaprnlem1.c
    hgmaprnlem1.p
    hgmaprnlem1.a
    hgmaprnlem1.g
    hgmaprnlem1.k
    hgmaprnlem1.k2
    hgmapdcl
    wph
    cC
    cD
    cS
    @4
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
    @11
    hdmapcl
    wph
    @5
    cQ
    wne
    @4
    c.0
    wne
    #
    wph
    @4
    cV
    @10
    cdif
    wcel
    @12
    hgmaprnlem1.t2
    @4
    cV
    c.0
    eldifsni
    syl
    wph
    @5
    cQ
    @4
    c.0
    wph
    cC
    cQ
    cS
    @4
    cU
    cH
    cK
    cV
    cW
    c.0
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.v
    hgmaprnlem1.o
    hgmaprnlem1.c
    hgmaprnlem1.q
    hgmaprnlem1.s
    hgmaprnlem1.k
    @11
    hdmapeq0
    necon3bid
    mpbird
    lvecvscan2
    mpbid
    wph
    cG
    cB
    wfn
    @1
    cB
    wcel
    @2
    @3
    wcel
    wph
    cB
    cR
    cU
    cG
    cH
    cK
    cW
    hgmaprnlem1.h
    hgmaprnlem1.u
    hgmaprnlem1.r
    hgmaprnlem1.b
    hgmaprnlem1.g
    hgmaprnlem1.k
    hgmapfnN
    hgmaprnlem1.k2
    cB
    @1
    cG
    fnfvelrn
    syl2anc
    eqeltrd
end
