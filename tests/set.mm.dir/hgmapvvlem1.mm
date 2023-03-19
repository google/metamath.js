include "cfv.mm"
include "co.mm"
include "crg.mm"
include "wcel.mm"
include "wceq.mm"
include "clmod.mm"
include "dvhlmod.mm"
include "lmodring.mm"
include "syl.mm"
include "csn.mm"
include "eldifad.mm"
include "hgmapcl.mm"
include "cdr.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "cdif.mm"
include "eldifsni.mm"
include "hgmapeq0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
include "ringass.mm"
include "syl13anc.mm"
include "drnginvrr.mm"
include "oveq2d.mm"
include "ringridm.mm"
include "syl2anc.mm"
include "3eqtrrd.mm"
include "fveq2d.mm"
include "hgmapmul.mm"
include "eqtr3d.mm"
include "cplusg.mm"
include "csg.mm"
include "eqid.mm"
include "hdmapglem5.mm"
include "eqtr4d.mm"
include "hdmapinvlem4.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem hgmapvvlem1
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
  let cY: class Y
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
  assume hdmapglem6.y: |- ( ph -> Y e. ( B \ { .0. } ) )
  assume hdmapglem6.yx: |- ( ph -> ( Y .X. ( G ` X ) ) = .1. )


  assert |- ( ph -> ( G ` ( G ` X ) ) = X )

  proof
    wph
    cX
    cG
    cfv
    #
    cG
    cfv
    #
    @1
    cY
    cG
    cfv
    #
    c.xp
    co
    #
    @2
    cN
    cfv
    #
    c.xp
    co
    #
    cX
    @2
    c.xp
    co
    #
    @4
    c.xp
    co
    #
    cX
    wph
    @5
    @1
    @2
    @4
    c.xp
    co
    #
    c.xp
    co
    #
    @1
    c.1
    c.xp
    co
    #
    @1
    wph
    cR
    crg
    wcel
    #
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    @4
    cB
    wcel
    #
    @5
    @9
    wceq
    wph
    cU
    clmod
    wcel
    @11
    wph
    cU
    cH
    cK
    cW
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.k
    dvhlmod
    cR
    cU
    hdmapglem6.r
    lmodring
    syl
    #
    wph
    cB
    cR
    cU
    @0
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
    c.0
    csn
    #
    hdmapglem6.x
    eldifad
    #
    hgmapcl
    #
    hgmapcl
    #
    wph
    cB
    cR
    cU
    cY
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
    cY
    cB
    @16
    hdmapglem6.y
    eldifad
    #
    hgmapcl
    #
    wph
    cR
    cdr
    wcel
    #
    @13
    @2
    c.0
    wne
    #
    @14
    wph
    cU
    clvec
    wcel
    @22
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
    @21
    wph
    @23
    cY
    c.0
    wne
    #
    wph
    cY
    cB
    @16
    cdif
    wcel
    @25
    hdmapglem6.y
    cY
    cB
    c.0
    eldifsni
    syl
    wph
    @2
    c.0
    cY
    c.0
    wph
    cB
    cR
    cU
    cG
    cH
    cK
    cW
    cY
    c.0
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.r
    hdmapglem6.b
    hdmapglem6.z
    hdmapglem6.g
    hdmapglem6.k
    @20
    hgmapeq0
    necon3bid
    mpbird
    #
    cB
    cR
    cN
    @2
    c.0
    hdmapglem6.b
    hdmapglem6.z
    hdmapglem6.n
    drnginvrcl
    syl3anc
    #
    cB
    cR
    c.xp
    @1
    @2
    @4
    hdmapglem6.b
    hdmapglem6.t
    ringass
    syl13anc
    wph
    @8
    c.1
    @1
    c.xp
    wph
    @22
    @13
    @23
    @8
    c.1
    wceq
    @24
    @21
    @26
    cB
    cR
    c.xp
    c.1
    cN
    @2
    c.0
    hdmapglem6.b
    hdmapglem6.z
    hdmapglem6.t
    hdmapglem6.i
    hdmapglem6.n
    drnginvrr
    syl3anc
    #
    oveq2d
    wph
    @11
    @12
    @10
    @1
    wceq
    @15
    @19
    cB
    cR
    c.xp
    c.1
    @1
    hdmapglem6.b
    hdmapglem6.t
    hdmapglem6.i
    ringridm
    syl2anc
    3eqtrrd
    wph
    @3
    @6
    @4
    c.xp
    wph
    @3
    cD
    cC
    cS
    cfv
    cfv
    #
    @6
    wph
    c.1
    cG
    cfv
    #
    @3
    @29
    wph
    cY
    @0
    c.xp
    co
    #
    cG
    cfv
    @30
    @3
    wph
    @31
    c.1
    cG
    hdmapglem6.yx
    fveq2d
    wph
    cB
    cR
    c.xp
    cU
    cG
    cH
    cK
    cW
    cY
    @0
    hdmapglem6.h
    hdmapglem6.u
    hdmapglem6.r
    hdmapglem6.b
    hdmapglem6.t
    hdmapglem6.g
    hdmapglem6.k
    @20
    @18
    hgmapmul
    eqtr3d
    wph
    cC
    cD
    cS
    cfv
    cfv
    #
    cG
    cfv
    @30
    @29
    wph
    @32
    c.1
    cG
    hdmapglem6.cd
    fveq2d
    wph
    cB
    cC
    cD
    cU
    cplusg
    cfv
    #
    cR
    cS
    c.x
    c.xp
    cU
    cE
    cG
    cH
    cY
    cX
    cK
    cU
    csg
    cfv
    #
    cO
    cV
    cW
    c.0
    hdmapglem6.h
    hdmapglem6.e
    hdmapglem6.o
    hdmapglem6.u
    hdmapglem6.v
    @33
    eqid
    #
    @34
    eqid
    #
    hdmapglem6.q
    hdmapglem6.r
    hdmapglem6.b
    hdmapglem6.t
    hdmapglem6.z
    hdmapglem6.s
    hdmapglem6.g
    hdmapglem6.k
    hdmapglem6.c
    hdmapglem6.d
    @20
    @17
    hdmapglem5
    eqtr3d
    eqtr3d
    wph
    cB
    cC
    cD
    @33
    cR
    cS
    c.x
    c.xp
    cU
    cE
    cG
    cH
    cY
    cX
    cK
    @34
    cO
    cV
    cW
    c.0
    hdmapglem6.h
    hdmapglem6.e
    hdmapglem6.o
    hdmapglem6.u
    hdmapglem6.v
    @35
    @36
    hdmapglem6.q
    hdmapglem6.r
    hdmapglem6.b
    hdmapglem6.t
    hdmapglem6.z
    hdmapglem6.s
    hdmapglem6.g
    hdmapglem6.k
    hdmapglem6.c
    hdmapglem6.d
    @20
    @17
    wph
    @31
    c.1
    @32
    hdmapglem6.yx
    hdmapglem6.cd
    eqtr4d
    hdmapinvlem4
    eqtr4d
    oveq1d
    wph
    @7
    cX
    @8
    c.xp
    co
    #
    cX
    c.1
    c.xp
    co
    #
    cX
    wph
    @11
    cX
    cB
    wcel
    #
    @13
    @14
    @7
    @37
    wceq
    @15
    @17
    @21
    @27
    cB
    cR
    c.xp
    cX
    @2
    @4
    hdmapglem6.b
    hdmapglem6.t
    ringass
    syl13anc
    wph
    @8
    c.1
    cX
    c.xp
    @28
    oveq2d
    wph
    @11
    @39
    @38
    cX
    wceq
    @15
    @17
    cB
    cR
    c.xp
    c.1
    cX
    hdmapglem6.b
    hdmapglem6.t
    hdmapglem6.i
    ringridm
    syl2anc
    3eqtrd
    3eqtrd
end
