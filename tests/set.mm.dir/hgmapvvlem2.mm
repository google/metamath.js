include "cfv.mm"
include "wcel.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "cdr.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "eldifad.mm"
include "hgmapcl.mm"
include "eldifsni.mm"
include "hgmapeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
include "drnginvrn0.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "co.mm"
include "wceq.mm"
include "drnginvrl.mm"
include "hgmapvvlem1.mm"

theorem hgmapvvlem2
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let c.xp: class .X.
  let cU: class U
  let c.1: class .1.
  let cE: class E
  let cG: class G
  let cH: class H
  let cK: class K
  let cN: class N
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let c.0: class .0.
  assume hdmapglem6.h: |- H = ( LHyp ` K )
  assume hdmapglem6.e: |- E = <. ( _I |` ( Base ` K ) ) , ( _I |` ( ( LTrn ` K ) ` W ) ) >.
  assume hdmapglem6.o: |- O = ( ( ocH ` K ) ` W )
  assume hdmapglem6.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapglem6.v: |- V = ( Base ` U )
  assume hdmapglem6.q: |- .x. = ( .s ` U )
  assume hdmapglem6.r: |- R = ( Scalar ` U )
  assume hdmapglem6.b: |- B = ( Base ` R )
  assume hdmapglem6.t: |- .X. = ( .r ` R )
  assume hdmapglem6.z: |- .0. = ( 0g ` R )
  assume hdmapglem6.i: |- .1. = ( 1r ` R )
  assume hdmapglem6.n: |- N = ( invr ` R )
  assume hdmapglem6.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapglem6.g: |- G = ( ( HGMap ` K ) ` W )
  assume hdmapglem6.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapglem6.x: |- ( ph -> X e. ( B \ { .0. } ) )
  assume hdmapglem6.c: |- ( ph -> C e. ( O ` { E } ) )
  assume hdmapglem6.d: |- ( ph -> D e. ( O ` { E } ) )
  assume hdmapglem6.cd: |- ( ph -> ( ( S ` D ) ` C ) = .1. )


  assert |- ( ph -> ( G ` ( G ` X ) ) = X )

  proof
    wph
    cB
    cC
    cD
    cR
    cS
    c.x
    c.xp
    cU
    c.1
    cE
    cG
    cH
    cK
    cN
    cO
    cV
    cW
    cX
    cX
    cG
    cfv
    #
    cN
    cfv
    #
    c.0
    hdmapglem6.h
    hdmapglem6.e
    hdmapglem6.o
    hdmapglem6.u
    hdmapglem6.v
    hdmapglem6.q
    hdmapglem6.r
    hdmapglem6.b
    hdmapglem6.t
    hdmapglem6.z
    hdmapglem6.i
    hdmapglem6.n
    hdmapglem6.s
    hdmapglem6.g
    hdmapglem6.k
    hdmapglem6.x
    hdmapglem6.c
    hdmapglem6.d
    hdmapglem6.cd
    wph
    @1
    cB
    wcel
    #
    @1
    c.0
    wne
    #
    @1
    cB
    c.0
    csn
    #
    cdif
    #
    wcel
    wph
    cR
    cdr
    wcel
    #
    @0
    cB
    wcel
    #
    @0
    c.0
    wne
    #
    @2
    wph
    cU
    clvec
    wcel
    @6
    wph
    cU
    cH
    cK
    cW
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.k
    dvhlvec
    cR
    cU
    hdmapglem6.r
    lvecdrng
    syl
    #
    wph
    cB
    cR
    cU
    cX
    cG
    cH
    cK
    cW
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.r
    hdmapglem6.b
    hdmapglem6.g
    hdmapglem6.k
    wph
    cX
    cB
    @4
    hdmapglem6.x
    eldifad
    #
    hgmapcl
    #
    wph
    @8
    cX
    c.0
    wne
    #
    wph
    cX
    @5
    wcel
    @12
    hdmapglem6.x
    cX
    cB
    c.0
    eldifsni
    syl
    wph
    @0
    c.0
    cX
    c.0
    wph
    cB
    cR
    cU
    cG
    cH
    cK
    cW
    cX
    c.0
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.r
    hdmapglem6.b
    hdmapglem6.z
    hdmapglem6.g
    hdmapglem6.k
    @10
    hgmapeq0
    necon3bid
    mpbird
    #
    cB
    cR
    cN
    @0
    c.0
    hdmapglem6.b
    hdmapglem6.z
    hdmapglem6.n
    drnginvrcl
    syl3anc
    wph
    @6
    @7
    @8
    @3
    @9
    @11
    @13
    cB
    cR
    cN
    @0
    c.0
    hdmapglem6.b
    hdmapglem6.z
    hdmapglem6.n
    drnginvrn0
    syl3anc
    @1
    cB
    c.0
    eldifsn
    sylanbrc
    wph
    @6
    @7
    @8
    @1
    @0
    c.xp
    co
    c.1
    wceq
    @9
    @11
    @13
    cB
    cR
    c.xp
    c.1
    cN
    @0
    c.0
    hdmapglem6.b
    hdmapglem6.z
    hdmapglem6.t
    hdmapglem6.i
    hdmapglem6.n
    drnginvrl
    syl3anc
    hgmapvvlem1
end
