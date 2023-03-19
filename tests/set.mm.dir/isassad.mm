include "clmod.mm"
include "wcel.mm"
include "crg.mm"
include "csca.mm"
include "cfv.mm"
include "ccrg.mm"
include "w3a.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "cmulr.mm"
include "wceq.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "casa.mm"
include "eqeltrrd.mm"
include "3jca.mm"
include "jca.mm"
include "ralrimivvva.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "oveqd.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "raleqbidv.mm"
include "mpbid.mm"
include "eqid.mm"
include "isassa.mm"
include "sylanbrc.mm"

theorem isassad
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.x: class .x.
  let c.xp: class .X.
  let cF: class F
  let cV: class V
  let cW: class W
  let vr: setvar r
  assume isassad.v: |- ( ph -> V = ( Base ` W ) )
  assume isassad.f: |- ( ph -> F = ( Scalar ` W ) )
  assume isassad.b: |- ( ph -> B = ( Base ` F ) )
  assume isassad.s: |- ( ph -> .x. = ( .s ` W ) )
  assume isassad.t: |- ( ph -> .X. = ( .r ` W ) )
  assume isassad.1: |- ( ph -> W e. LMod )
  assume isassad.2: |- ( ph -> W e. Ring )
  assume isassad.3: |- ( ph -> F e. CRing )
  assume isassad.4: |- ( ( ph /\ ( r e. B /\ x e. V /\ y e. V ) ) -> ( ( r .x. x ) .X. y ) = ( r .x. ( x .X. y ) ) )
  assume isassad.5: |- ( ( ph /\ ( r e. B /\ x e. V /\ y e. V ) ) -> ( x .X. ( r .x. y ) ) = ( r .x. ( x .X. y ) ) )

  disjoint r x
  disjoint r y
  disjoint B r
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint ph r
  disjoint ph x
  disjoint ph y
  disjoint V x
  disjoint V y
  disjoint W r
  disjoint W x
  disjoint W y
  assert |- ( ph -> W e. AssAlg )

  proof
    wph
    cW
    clmod
    wcel
    #
    cW
    crg
    wcel
    #
    cW
    csca
    cfv
    #
    ccrg
    wcel
    #
    w3a
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
    cmulr
    cfv
    #
    co
    #
    @4
    @5
    @8
    @9
    co
    #
    @6
    co
    #
    wceq
    #
    @5
    @4
    @8
    @6
    co
    #
    @9
    co
    #
    @12
    wceq
    #
    wa
    #
    vy
    cW
    cbs
    cfv
    #
    wral
    #
    vx
    @18
    wral
    #
    vr
    @2
    cbs
    cfv
    #
    wral
    #
    cW
    casa
    wcel
    wph
    @0
    @1
    @3
    isassad.1
    isassad.2
    wph
    cF
    @2
    ccrg
    isassad.f
    isassad.3
    eqeltrrd
    3jca
    wph
    @4
    @5
    c.x
    co
    #
    @8
    c.xp
    co
    #
    @4
    @5
    @8
    c.xp
    co
    #
    c.x
    co
    #
    wceq
    #
    @5
    @4
    @8
    c.x
    co
    #
    c.xp
    co
    #
    @26
    wceq
    #
    wa
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
    cB
    wral
    @22
    wph
    @31
    vr
    vx
    vy
    cB
    cV
    cV
    wph
    @4
    cB
    wcel
    @5
    cV
    wcel
    @8
    cV
    wcel
    w3a
    wa
    @27
    @30
    isassad.4
    isassad.5
    jca
    ralrimivvva
    wph
    @33
    @20
    vr
    cB
    @21
    wph
    cB
    cF
    cbs
    cfv
    @21
    isassad.b
    wph
    cF
    @2
    cbs
    isassad.f
    fveq2d
    eqtrd
    wph
    @32
    @19
    vx
    cV
    @18
    isassad.v
    wph
    @31
    @17
    vy
    cV
    @18
    isassad.v
    wph
    @27
    @13
    @30
    @16
    wph
    @24
    @10
    @26
    @12
    wph
    @23
    @7
    @8
    @8
    c.xp
    @9
    isassad.t
    wph
    c.x
    @6
    @4
    @5
    isassad.s
    oveqd
    wph
    @8
    eqidd
    oveq123d
    wph
    @4
    @4
    @25
    @11
    c.x
    @6
    isassad.s
    wph
    @4
    eqidd
    wph
    c.xp
    @9
    @5
    @8
    isassad.t
    oveqd
    oveq123d
    #
    eqeq12d
    wph
    @29
    @15
    @26
    @12
    wph
    @5
    @5
    @28
    @14
    c.xp
    @9
    isassad.t
    wph
    @5
    eqidd
    wph
    c.x
    @6
    @4
    @8
    isassad.s
    oveqd
    oveq123d
    @34
    eqeq12d
    anbi12d
    raleqbidv
    raleqbidv
    raleqbidv
    mpbid
    vx
    vy
    @21
    @6
    @9
    @2
    @18
    cW
    vr
    @18
    eqid
    @2
    eqid
    @21
    eqid
    @6
    eqid
    @9
    eqid
    isassa
    sylanbrc
end
