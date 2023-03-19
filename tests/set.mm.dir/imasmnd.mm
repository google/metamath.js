include "cmnd.mm"
include "cv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "cbs.mm"
include "cfv.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "wceq.mm"
include "eleqtrd.mm"
include "simp3.mm"
include "eqid.mm"
include "mndcl.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "wa.mm"
include "adantr.mm"
include "3adant3r3.mm"
include "simpr3.mm"
include "mndass.mm"
include "syl13anc.mm"
include "fveq2d.mm"
include "mndidcl.mm"
include "syl.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "mndlid.mm"
include "syl2anc.mm"
include "mndrid.mm"
include "imasmnd2.mm"

theorem imasmnd
  let wph: wff ph
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cU: class U
  let cF: class F
  let cV: class V
  let c.0: class .0.
  let vq: setvar q
  let vp: setvar p
  let va: setvar a
  let vb: setvar b
  let vx: setvar x
  let vy: setvar y
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vz: setvar z
  assume imasmnd.u: |- ( ph -> U = ( F "s R ) )
  assume imasmnd.v: |- ( ph -> V = ( Base ` R ) )
  assume imasmnd.p: |- .+ = ( +g ` R )
  assume imasmnd.f: |- ( ph -> F : V -onto-> B )
  assume imasmnd.e: |- ( ( ph /\ ( a e. V /\ b e. V ) /\ ( p e. V /\ q e. V ) ) -> ( ( ( F ` a ) = ( F ` p ) /\ ( F ` b ) = ( F ` q ) ) -> ( F ` ( a .+ b ) ) = ( F ` ( p .+ q ) ) ) )
  assume imasmnd.r: |- ( ph -> R e. Mnd )
  assume imasmnd.z: |- .0. = ( 0g ` R )

  disjoint p q
  disjoint .+ p
  disjoint .+ q
  disjoint a b
  disjoint a p
  disjoint a q
  disjoint a ph
  disjoint b p
  disjoint b q
  disjoint b ph
  disjoint p ph
  disjoint ph q
  disjoint U a
  disjoint U b
  disjoint U p
  disjoint U q
  disjoint .0. p
  disjoint .0. q
  disjoint B p
  disjoint B q
  disjoint F a
  disjoint F b
  disjoint F p
  disjoint F q
  disjoint R p
  disjoint R q
  disjoint V a
  disjoint V b
  disjoint V p
  disjoint V q
  disjoint p x
  disjoint p y
  disjoint q x
  disjoint q y
  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b u
  disjoint b v
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint p z
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint q z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint ph v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint ph w
  disjoint x z
  disjoint ph x
  disjoint y z
  disjoint ph y
  disjoint ph z
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U x
  disjoint U y
  disjoint U z
  disjoint .0. u
  disjoint .0. x
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint F u
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint V x
  disjoint V y
  disjoint V z
  assert |- ( ph -> ( U e. Mnd /\ ( F ` .0. ) = ( 0g ` U ) ) )

  proof
    wph
    vx
    vy
    vz
    cB
    c.pl
    cR
    cU
    cF
    cV
    cmnd
    c.0
    vq
    vp
    va
    vb
    imasmnd.u
    imasmnd.v
    imasmnd.p
    imasmnd.f
    imasmnd.e
    imasmnd.r
    wph
    vx
    cv
    #
    cV
    wcel
    #
    vy
    cv
    #
    cV
    wcel
    #
    w3a
    #
    @0
    @2
    c.pl
    co
    #
    cR
    cbs
    cfv
    #
    cV
    @4
    cR
    cmnd
    wcel
    #
    @0
    @6
    wcel
    #
    @2
    @6
    wcel
    #
    @5
    @6
    wcel
    wph
    @1
    @7
    @3
    imasmnd.r
    3ad2ant1
    @4
    @0
    cV
    @6
    wph
    @1
    @3
    simp2
    wph
    @1
    cV
    @6
    wceq
    #
    @3
    imasmnd.v
    3ad2ant1
    #
    eleqtrd
    #
    @4
    @2
    cV
    @6
    wph
    @1
    @3
    simp3
    @11
    eleqtrd
    #
    @6
    c.pl
    cR
    @0
    @2
    @6
    eqid
    #
    imasmnd.p
    mndcl
    syl3anc
    @11
    eleqtrrd
    wph
    @1
    @3
    vz
    cv
    #
    cV
    wcel
    #
    w3a
    #
    wa
    #
    @5
    @15
    c.pl
    co
    #
    @0
    @2
    @15
    c.pl
    co
    c.pl
    co
    #
    cF
    @18
    @7
    @8
    @9
    @15
    @6
    wcel
    @19
    @20
    wceq
    wph
    @7
    @17
    imasmnd.r
    adantr
    wph
    @1
    @3
    @8
    @16
    @12
    3adant3r3
    wph
    @1
    @3
    @9
    @16
    @13
    3adant3r3
    @18
    @15
    cV
    @6
    wph
    @1
    @3
    @16
    simpr3
    wph
    @10
    @17
    imasmnd.v
    adantr
    eleqtrd
    @6
    c.pl
    cR
    @0
    @2
    @15
    @14
    imasmnd.p
    mndass
    syl13anc
    fveq2d
    wph
    c.0
    @6
    cV
    wph
    @7
    c.0
    @6
    wcel
    imasmnd.r
    @6
    cR
    c.0
    @14
    imasmnd.z
    mndidcl
    syl
    imasmnd.v
    eleqtrrd
    wph
    @1
    wa
    #
    c.0
    @0
    c.pl
    co
    #
    @0
    cF
    @21
    @7
    @8
    @22
    @0
    wceq
    wph
    @7
    @1
    imasmnd.r
    adantr
    #
    wph
    @1
    @8
    wph
    cV
    @6
    @0
    imasmnd.v
    eleq2d
    biimpa
    #
    @6
    c.pl
    cR
    @0
    c.0
    @14
    imasmnd.p
    imasmnd.z
    mndlid
    syl2anc
    fveq2d
    @21
    @0
    c.0
    c.pl
    co
    #
    @0
    cF
    @21
    @7
    @8
    @25
    @0
    wceq
    @23
    @24
    @6
    c.pl
    cR
    @0
    c.0
    @14
    imasmnd.p
    imasmnd.z
    mndrid
    syl2anc
    fveq2d
    imasmnd2
end
