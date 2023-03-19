include "cfv.mm"
include "co.mm"
include "fveq2i.mm"
include "cmulr.mm"
include "cbs.mm"
include "eqid.mm"
include "csn.mm"
include "eldifad.mm"
include "cdr.mm"
include "wcel.mm"
include "c0g.mm"
include "wne.mm"
include "clvec.mm"
include "dvhlvec.mm"
include "lvecdrng.mm"
include "syl.mm"
include "hdmapipcl.mm"
include "cdif.mm"
include "eldifsni.mm"
include "hdmapip0.mm"
include "necon3bid.mm"
include "mpbird.mm"
include "drnginvrcl.mm"
include "syl3anc.mm"
include "hdmaplnm1.mm"
include "wceq.mm"
include "drnginvrl.mm"
include "eqtrd.mm"
include "syl5eq.mm"

theorem hdmapip1
  let wph: wff ph
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let cH: class H
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let c.0: class .0.
  assume hdmapip1.h: |- H = ( LHyp ` K )
  assume hdmapip1.u: |- U = ( ( DVecH ` K ) ` W )
  assume hdmapip1.v: |- V = ( Base ` U )
  assume hdmapip1.t: |- .x. = ( .s ` U )
  assume hdmapip1.o: |- .0. = ( 0g ` U )
  assume hdmapip1.r: |- R = ( Scalar ` U )
  assume hdmapip1.i: |- .1. = ( 1r ` R )
  assume hdmapip1.n: |- N = ( invr ` R )
  assume hdmapip1.s: |- S = ( ( HDMap ` K ) ` W )
  assume hdmapip1.k: |- ( ph -> ( K e. HL /\ W e. H ) )
  assume hdmapip1.x: |- ( ph -> X e. ( V \ { .0. } ) )
  assume hdmapip1.y: |- Y = ( ( N ` ( ( S ` X ) ` X ) ) .x. X )


  assert |- ( ph -> ( ( S ` X ) ` Y ) = .1. )

  proof
    wph
    cY
    cX
    cS
    cfv
    #
    cfv
    cX
    @0
    cfv
    #
    cN
    cfv
    #
    cX
    c.x
    co
    #
    @0
    cfv
    #
    c.1
    cY
    @3
    @0
    hdmapip1.y
    fveq2i
    wph
    @4
    @2
    @1
    cR
    cmulr
    cfv
    #
    co
    #
    c.1
    wph
    @2
    cR
    cbs
    cfv
    #
    cR
    cS
    c.x
    @5
    cU
    cH
    cK
    cV
    cW
    cX
    cX
    hdmapip1.h
    hdmapip1.u
    hdmapip1.v
    hdmapip1.t
    hdmapip1.r
    @7
    eqid
    #
    @5
    eqid
    #
    hdmapip1.s
    hdmapip1.k
    wph
    cX
    cV
    c.0
    csn
    #
    hdmapip1.x
    eldifad
    #
    @11
    wph
    cR
    cdr
    wcel
    #
    @1
    @7
    wcel
    #
    @1
    cR
    c0g
    cfv
    #
    wne
    #
    @2
    @7
    wcel
    wph
    cU
    clvec
    wcel
    @12
    wph
    cU
    cH
    cK
    cW
    hdmapip1.h
    hdmapip1.u
    hdmapip1.k
    dvhlvec
    cR
    cU
    hdmapip1.r
    lvecdrng
    syl
    #
    wph
    @7
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    cX
    cX
    hdmapip1.h
    hdmapip1.u
    hdmapip1.v
    hdmapip1.r
    @8
    hdmapip1.s
    hdmapip1.k
    @11
    @11
    hdmapipcl
    #
    wph
    @15
    cX
    c.0
    wne
    #
    wph
    cX
    cV
    @10
    cdif
    wcel
    @18
    hdmapip1.x
    cX
    cV
    c.0
    eldifsni
    syl
    wph
    @1
    @14
    cX
    c.0
    wph
    cR
    cS
    cU
    cH
    cK
    cV
    cW
    cX
    c.0
    @14
    hdmapip1.h
    hdmapip1.u
    hdmapip1.v
    hdmapip1.o
    hdmapip1.r
    @14
    eqid
    #
    hdmapip1.s
    hdmapip1.k
    @11
    hdmapip0
    necon3bid
    mpbird
    #
    @7
    cR
    cN
    @1
    @14
    @8
    @19
    hdmapip1.n
    drnginvrcl
    syl3anc
    hdmaplnm1
    wph
    @12
    @13
    @15
    @6
    c.1
    wceq
    @16
    @17
    @20
    @7
    cR
    @5
    c.1
    cN
    @1
    @14
    @8
    @19
    @9
    hdmapip1.i
    hdmapip1.n
    drnginvrl
    syl3anc
    eqtrd
    syl5eq
end
