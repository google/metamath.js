include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "csubg.mm"
include "cfv.mm"
include "wb.mm"
include "lsmelval.mm"
include "syl2anc.mm"
include "biimpa.mm"
include "reeanv.mm"
include "eqtr2.mm"
include "ad2antrr.mm"
include "cin.mm"
include "csn.mm"
include "wss.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simprl.mm"
include "simprr.mm"
include "subgdisjb.mm"
include "simpl.mm"
include "syl6bi.mm"
include "syl5.mm"
include "rexlimdvva.mm"
include "syl5bir.mm"
include "ralrimivva.mm"
include "adantr.mm"
include "oveq1.mm"
include "eqeq2d.mm"
include "rexbidv.mm"
include "oveq2.mm"
include "cbvrexv.mm"
include "syl6bb.mm"
include "reu4.mm"
include "sylanbrc.mm"

theorem pj1eu
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.po: class .(+)
  let cT: class T
  let cU: class U
  let cG: class G
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vu: setvar u
  let vv: setvar v
  let vz: setvar z
  let cP: class P
  assume pj1eu.a: |- .+ = ( +g ` G )
  assume pj1eu.s: |- .(+) = ( LSSum ` G )
  assume pj1eu.o: |- .0. = ( 0g ` G )
  assume pj1eu.z: |- Z = ( Cntz ` G )
  assume pj1eu.2: |- ( ph -> T e. ( SubGrp ` G ) )
  assume pj1eu.3: |- ( ph -> U e. ( SubGrp ` G ) )
  assume pj1eu.4: |- ( ph -> ( T i^i U ) = { .0. } )
  assume pj1eu.5: |- ( ph -> T C_ ( Z ` U ) )

  disjoint x y
  disjoint .+ x
  disjoint .+ y
  disjoint .(+) x
  disjoint .(+) y
  disjoint ph x
  disjoint ph y
  disjoint G x
  disjoint G y
  disjoint T x
  disjoint T y
  disjoint U x
  disjoint U y
  disjoint X x
  disjoint X y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint .+ u
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint .+ v
  disjoint x z
  disjoint y z
  disjoint .+ z
  disjoint .(+) u
  disjoint .(+) v
  disjoint .(+) z
  disjoint P v
  disjoint P x
  disjoint P y
  disjoint ph u
  disjoint ph v
  disjoint ph z
  disjoint G u
  disjoint G v
  disjoint G z
  disjoint T u
  disjoint T v
  disjoint T z
  disjoint U u
  disjoint U v
  disjoint U z
  disjoint X u
  disjoint X v
  assert |- ( ( ph /\ X e. ( T .(+) U ) ) -> E! x e. T E. y e. U X = ( x .+ y ) )

  proof
    wph
    cX
    cT
    cU
    c.po
    co
    wcel
    #
    wa
    cX
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vy
    cU
    wrex
    #
    vx
    cT
    wrex
    #
    @5
    cX
    vu
    cv
    #
    vv
    cv
    #
    c.pl
    co
    #
    wceq
    #
    vv
    cU
    wrex
    #
    wa
    #
    @1
    @7
    wceq
    #
    wi
    #
    vu
    cT
    wral
    vx
    cT
    wral
    #
    @5
    vx
    cT
    wreu
    wph
    @0
    @6
    wph
    cT
    cG
    csubg
    cfv
    #
    wcel
    #
    cU
    @16
    wcel
    #
    @0
    @6
    wb
    pj1eu.2
    pj1eu.3
    vx
    vy
    c.pl
    c.po
    cT
    cU
    cG
    cX
    pj1eu.a
    pj1eu.s
    lsmelval
    syl2anc
    biimpa
    wph
    @15
    @0
    wph
    @14
    vx
    vu
    cT
    cT
    @12
    @4
    @10
    wa
    #
    vv
    cU
    wrex
    vy
    cU
    wrex
    wph
    @1
    cT
    wcel
    #
    @7
    cT
    wcel
    #
    wa
    #
    wa
    #
    @13
    @4
    @10
    vy
    vv
    cU
    cU
    reeanv
    @23
    @19
    @13
    vy
    vv
    cU
    cU
    @19
    @3
    @9
    wceq
    #
    @23
    @2
    cU
    wcel
    #
    @8
    cU
    wcel
    #
    wa
    #
    wa
    #
    @13
    cX
    @3
    @9
    eqtr2
    @28
    @24
    @13
    @2
    @8
    wceq
    #
    wa
    @13
    @28
    @1
    @2
    @7
    @8
    c.pl
    cT
    cU
    cG
    c.0
    cZ
    pj1eu.a
    pj1eu.o
    pj1eu.z
    wph
    @17
    @22
    @27
    pj1eu.2
    ad2antrr
    wph
    @18
    @22
    @27
    pj1eu.3
    ad2antrr
    wph
    cT
    cU
    cin
    c.0
    csn
    wceq
    @22
    @27
    pj1eu.4
    ad2antrr
    wph
    cT
    cU
    cZ
    cfv
    wss
    @22
    @27
    pj1eu.5
    ad2antrr
    wph
    @20
    @21
    @27
    simplrl
    wph
    @20
    @21
    @27
    simplrr
    @23
    @25
    @26
    simprl
    @23
    @25
    @26
    simprr
    subgdisjb
    @13
    @29
    simpl
    syl6bi
    syl5
    rexlimdvva
    syl5bir
    ralrimivva
    adantr
    @5
    @11
    vx
    vu
    cT
    @13
    @5
    cX
    @7
    @2
    c.pl
    co
    #
    wceq
    #
    vy
    cU
    wrex
    @11
    @13
    @4
    @31
    vy
    cU
    @13
    @3
    @30
    cX
    @1
    @7
    @2
    c.pl
    oveq1
    eqeq2d
    rexbidv
    @31
    @10
    vy
    vv
    cU
    @29
    @30
    @9
    cX
    @2
    @8
    @7
    c.pl
    oveq2
    eqeq2d
    cbvrexv
    syl6bb
    reu4
    sylanbrc
end
