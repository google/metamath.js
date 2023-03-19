include "cv.mm"
include "cplusg.mm"
include "cfv.mm"
include "co.mm"
include "cbs.mm"
include "wcel.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "cmnd.mm"
include "3expb.mm"
include "simpll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "syl13anc.mm"
include "ralrimiva.mm"
include "jca.mm"
include "ralrimivva.mm"
include "oveqd.mm"
include "eleq12d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "mpbid.mm"
include "eleqtrd.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "syldan.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "eqid.mm"
include "ismnd.mm"
include "sylanbrc.mm"

theorem ismndd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let c.0: class .0.
  let vu: setvar u
  assume ismndd.b: |- ( ph -> B = ( Base ` G ) )
  assume ismndd.p: |- ( ph -> .+ = ( +g ` G ) )
  assume ismndd.c: |- ( ( ph /\ x e. B /\ y e. B ) -> ( x .+ y ) e. B )
  assume ismndd.a: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) ) -> ( ( x .+ y ) .+ z ) = ( x .+ ( y .+ z ) ) )
  assume ismndd.z: |- ( ph -> .0. e. B )
  assume ismndd.i: |- ( ( ph /\ x e. B ) -> ( .0. .+ x ) = x )
  assume ismndd.j: |- ( ( ph /\ x e. B ) -> ( x .+ .0. ) = x )

  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint .0. x
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint .0. u
  assert |- ( ph -> G e. Mnd )

  proof
    wph
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    cbs
    cfv
    #
    wcel
    #
    @3
    vz
    cv
    #
    @2
    co
    #
    @0
    @1
    @6
    @2
    co
    #
    @2
    co
    #
    wceq
    #
    vz
    @4
    wral
    #
    wa
    #
    vy
    @4
    wral
    #
    vx
    @4
    wral
    #
    vu
    cv
    #
    @0
    @2
    co
    #
    @0
    wceq
    #
    @0
    @15
    @2
    co
    #
    @0
    wceq
    #
    wa
    #
    vx
    @4
    wral
    #
    vu
    @4
    wrex
    #
    cG
    cmnd
    wcel
    wph
    @0
    @1
    c.pl
    co
    #
    cB
    wcel
    #
    @23
    @6
    c.pl
    co
    #
    @0
    @1
    @6
    c.pl
    co
    #
    c.pl
    co
    #
    wceq
    #
    vz
    cB
    wral
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    @14
    wph
    @30
    vx
    vy
    cB
    cB
    wph
    @0
    cB
    wcel
    #
    @1
    cB
    wcel
    #
    wa
    #
    wa
    #
    @24
    @29
    wph
    @32
    @33
    @24
    ismndd.c
    3expb
    @35
    @28
    vz
    cB
    @35
    @6
    cB
    wcel
    #
    wa
    wph
    @32
    @33
    @36
    @28
    wph
    @34
    @36
    simpll
    wph
    @32
    @33
    @36
    simplrl
    wph
    @32
    @33
    @36
    simplrr
    @35
    @36
    simpr
    ismndd.a
    syl13anc
    ralrimiva
    jca
    ralrimivva
    wph
    @31
    @13
    vx
    cB
    @4
    ismndd.b
    wph
    @30
    @12
    vy
    cB
    @4
    ismndd.b
    wph
    @24
    @5
    @29
    @11
    wph
    @23
    @3
    cB
    @4
    wph
    c.pl
    @2
    @0
    @1
    ismndd.p
    oveqd
    #
    ismndd.b
    eleq12d
    wph
    @28
    @10
    vz
    cB
    @4
    ismndd.b
    wph
    @25
    @7
    @27
    @9
    wph
    @23
    @3
    @6
    @6
    c.pl
    @2
    ismndd.p
    @37
    wph
    @6
    eqidd
    oveq123d
    wph
    @0
    @0
    @26
    @8
    c.pl
    @2
    ismndd.p
    wph
    @0
    eqidd
    wph
    c.pl
    @2
    @1
    @6
    ismndd.p
    oveqd
    oveq123d
    eqeq12d
    raleqbidv
    anbi12d
    raleqbidv
    raleqbidv
    mpbid
    wph
    c.0
    @4
    wcel
    c.0
    @0
    @2
    co
    #
    @0
    wceq
    #
    @0
    c.0
    @2
    co
    #
    @0
    wceq
    #
    wa
    #
    vx
    @4
    wral
    #
    @22
    wph
    c.0
    cB
    @4
    ismndd.z
    ismndd.b
    eleqtrd
    wph
    @42
    vx
    @4
    wph
    @0
    @4
    wcel
    #
    @32
    @42
    wph
    @32
    @44
    wph
    cB
    @4
    @0
    ismndd.b
    eleq2d
    biimpar
    wph
    @32
    wa
    #
    @39
    @41
    @45
    c.0
    @0
    c.pl
    co
    @38
    @0
    @45
    c.pl
    @2
    c.0
    @0
    wph
    c.pl
    @2
    wceq
    @32
    ismndd.p
    adantr
    #
    oveqd
    ismndd.i
    eqtr3d
    @45
    @0
    c.0
    c.pl
    co
    @40
    @0
    @45
    c.pl
    @2
    @0
    c.0
    @46
    oveqd
    ismndd.j
    eqtr3d
    jca
    syldan
    ralrimiva
    @21
    @43
    vu
    c.0
    @4
    @15
    c.0
    wceq
    #
    @20
    @42
    vx
    @4
    @47
    @17
    @39
    @19
    @41
    @47
    @16
    @38
    @0
    @15
    c.0
    @0
    @2
    oveq1
    eqeq1d
    @47
    @18
    @40
    @0
    @15
    c.0
    @0
    @2
    oveq2
    eqeq1d
    anbi12d
    ralbidv
    rspcev
    syl2anc
    @4
    @2
    vu
    cG
    vx
    vy
    vz
    @4
    eqid
    @2
    eqid
    ismnd
    sylanbrc
end
