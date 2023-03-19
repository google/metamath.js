include "clfn.mm"
include "cfv.mm"
include "wcel.mm"
include "cbs.mm"
include "csca.mm"
include "wf.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cplusg.mm"
include "cmulr.mm"
include "wceq.mm"
include "wral.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "feq23d.mm"
include "mpbid.mm"
include "ralrimivvva.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "wa.mm"
include "eqid.mm"
include "islfl.mm"
include "biimpar.mm"
include "syl12anc.mm"
include "eleqtrrd.mm"

theorem islfld
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cD: class D
  let c.pl: class .+
  let c.pd: class .+^
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cG: class G
  let cK: class K
  let cV: class V
  let cW: class W
  let cX: class X
  let vr: setvar r
  assume islfld.v: |- ( ph -> V = ( Base ` W ) )
  assume islfld.a: |- ( ph -> .+ = ( +g ` W ) )
  assume islfld.d: |- ( ph -> D = ( Scalar ` W ) )
  assume islfld.s: |- ( ph -> .x. = ( .s ` W ) )
  assume islfld.k: |- ( ph -> K = ( Base ` D ) )
  assume islfld.p: |- ( ph -> .+^ = ( +g ` D ) )
  assume islfld.t: |- ( ph -> .X. = ( .r ` D ) )
  assume islfld.f: |- ( ph -> F = ( LFnl ` W ) )
  assume islfld.u: |- ( ph -> G : V --> K )
  assume islfld.l: |- ( ( ph /\ ( r e. K /\ x e. V /\ y e. V ) ) -> ( G ` ( ( r .x. x ) .+ y ) ) = ( ( r .X. ( G ` x ) ) .+^ ( G ` y ) ) )
  assume islfld.w: |- ( ph -> W e. X )

  disjoint r x
  disjoint r y
  disjoint G r
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint K r
  disjoint K x
  disjoint K y
  disjoint V x
  disjoint V y
  disjoint W r
  disjoint W x
  disjoint W y
  disjoint ph r
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> G e. F )

  proof
    wph
    cG
    cW
    clfn
    cfv
    #
    cF
    wph
    cW
    cX
    wcel
    #
    cW
    cbs
    cfv
    #
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    cG
    wf
    #
    vr
    cv
    #
    vx
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    #
    vy
    cv
    #
    cW
    cplusg
    cfv
    #
    co
    #
    cG
    cfv
    #
    @6
    @7
    cG
    cfv
    #
    @3
    cmulr
    cfv
    #
    co
    #
    @10
    cG
    cfv
    #
    @3
    cplusg
    cfv
    #
    co
    #
    wceq
    #
    vy
    @2
    wral
    #
    vx
    @2
    wral
    #
    vr
    @4
    wral
    #
    cG
    @0
    wcel
    #
    islfld.w
    wph
    cV
    cK
    cG
    wf
    @5
    islfld.u
    wph
    cV
    cK
    @2
    @4
    cG
    islfld.v
    wph
    cK
    cD
    cbs
    cfv
    @4
    islfld.k
    wph
    cD
    @3
    cbs
    islfld.d
    fveq2d
    eqtrd
    #
    feq23d
    mpbid
    wph
    @6
    @7
    c.x
    co
    #
    @10
    c.pl
    co
    #
    cG
    cfv
    #
    @6
    @14
    c.xp
    co
    #
    @17
    c.pd
    co
    #
    wceq
    #
    vy
    cV
    wral
    #
    vx
    cV
    wral
    #
    vr
    cK
    wral
    @23
    wph
    @31
    vr
    vx
    vy
    cK
    cV
    cV
    islfld.l
    ralrimivvva
    wph
    @33
    @22
    vr
    cK
    @4
    @25
    wph
    @32
    @21
    vx
    cV
    @2
    islfld.v
    wph
    @31
    @20
    vy
    cV
    @2
    islfld.v
    wph
    @28
    @13
    @30
    @19
    wph
    @27
    @12
    cG
    wph
    @26
    @9
    @10
    @10
    c.pl
    @11
    islfld.a
    wph
    c.x
    @8
    @6
    @7
    islfld.s
    oveqd
    wph
    @10
    eqidd
    oveq123d
    fveq2d
    wph
    @29
    @16
    @17
    @17
    c.pd
    @18
    wph
    c.pd
    cD
    cplusg
    cfv
    @18
    islfld.p
    wph
    cD
    @3
    cplusg
    islfld.d
    fveq2d
    eqtrd
    wph
    c.xp
    @15
    @6
    @14
    wph
    c.xp
    cD
    cmulr
    cfv
    @15
    islfld.t
    wph
    cD
    @3
    cmulr
    islfld.d
    fveq2d
    eqtrd
    oveqd
    wph
    @17
    eqidd
    oveq123d
    eqeq12d
    raleqbidv
    raleqbidv
    raleqbidv
    mpbid
    @1
    @24
    @5
    @23
    wa
    vx
    vy
    @3
    @11
    @18
    @8
    @15
    @0
    cG
    @4
    @2
    cW
    cX
    vr
    @2
    eqid
    @11
    eqid
    @3
    eqid
    @8
    eqid
    @4
    eqid
    @18
    eqid
    @15
    eqid
    @0
    eqid
    islfl
    biimpar
    syl12anc
    islfld.f
    eleqtrrd
end
