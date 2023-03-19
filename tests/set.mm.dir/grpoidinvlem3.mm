include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "cbvrexv.mm"
include "ralbii.mm"
include "bitri.mm"
include "oveq2.mm"
include "rexbidv.mm"
include "rspccva.mm"
include "sylanb.mm"
include "adantll.mm"
include "grpocl.mm"
include "3expa.mm"
include "adantllr.mm"
include "biimpi.mm"
include "ad2antrl.mm"
include "ad2antrr.mm"
include "id.mm"
include "eqeq12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "adantr.mm"
include "pm3.22.mm"
include "an31s.mm"
include "adantlr.mm"
include "adantlll.mm"
include "anim1i.mm"
include "grpoidinvlem2.mm"
include "wi.mm"
include "3expb.mm"
include "ad2ant2rl.mm"
include "sylan2b.mm"
include "anass.mm"
include "an32s.mm"
include "ex.mm"
include "syldan.mm"
include "imp.mm"
include "grpoidinvlem1.mm"
include "sylan.mm"
include "exp43.mm"
include "rexlimdv.mm"
include "syl5.mm"
include "mpand.mm"
include "exp32.mm"
include "com34.mm"
include "imp32.mm"
include "impl.mm"
include "mpd.mm"
include "eqtr3d.mm"
include "ancld.mm"
include "reximdva.mm"

theorem grpoidinvlem3
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  let vw: setvar w
  let cB: class B
  let cC: class C
  let vu: setvar u
  assume grpfo.1: |- X = ran G
  assume grpidinvlem3.2: |- ( ph <-> A. x e. X ( U G x ) = x )
  assume grpidinvlem3.3: |- ( ps <-> A. x e. X E. z e. X ( z G x ) = U )

  disjoint x y
  disjoint x z
  disjoint U x
  disjoint y z
  disjoint U y
  disjoint U z
  disjoint ph y
  disjoint ps y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint U y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint U w
  disjoint ph w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C z
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint G u
  disjoint G w
  disjoint X u
  disjoint X w
  assert |- ( ( ( ( G e. GrpOp /\ U e. X ) /\ ( ph /\ ps ) ) /\ A e. X ) -> E. y e. X ( ( y G A ) = U /\ ( A G y ) = U ) )

  proof
    cG
    cgr
    wcel
    #
    cU
    cX
    wcel
    #
    wa
    #
    wph
    wps
    wa
    #
    wa
    #
    cA
    cX
    wcel
    #
    wa
    #
    vy
    cv
    #
    cA
    cG
    co
    #
    cU
    wceq
    #
    vy
    cX
    wrex
    #
    @9
    cA
    @7
    cG
    co
    #
    cU
    wceq
    #
    wa
    #
    vy
    cX
    wrex
    @3
    @5
    @10
    @2
    wps
    @5
    @10
    wph
    wps
    @7
    vx
    cv
    #
    cG
    co
    #
    cU
    wceq
    #
    vy
    cX
    wrex
    #
    vx
    cX
    wral
    #
    @5
    @10
    wps
    vz
    cv
    #
    @14
    cG
    co
    #
    cU
    wceq
    #
    vz
    cX
    wrex
    #
    vx
    cX
    wral
    #
    @18
    grpidinvlem3.3
    @22
    @17
    vx
    cX
    @21
    @16
    vz
    vy
    cX
    @19
    @7
    wceq
    @20
    @15
    cU
    @19
    @7
    @14
    cG
    oveq1
    eqeq1d
    cbvrexv
    ralbii
    bitri
    @17
    @10
    vx
    cA
    cX
    @14
    cA
    wceq
    #
    @16
    @9
    vy
    cX
    @24
    @15
    @8
    cU
    @14
    cA
    @7
    cG
    oveq2
    eqeq1d
    rexbidv
    rspccva
    sylanb
    adantll
    adantll
    @6
    @9
    @13
    vy
    cX
    @6
    @7
    cX
    wcel
    #
    wa
    #
    @9
    @12
    @26
    @9
    @12
    @26
    @9
    wa
    #
    cU
    @11
    cG
    co
    #
    @11
    cU
    @26
    @28
    @11
    wceq
    #
    @9
    @26
    @11
    cX
    wcel
    #
    cU
    @14
    cG
    co
    #
    @14
    wceq
    #
    vx
    cX
    wral
    #
    @29
    @2
    @5
    @25
    @30
    @3
    @0
    @5
    @25
    @30
    @1
    @0
    @5
    @25
    @30
    cA
    @7
    cG
    cX
    grpfo.1
    grpocl
    #
    3expa
    adantllr
    adantllr
    @4
    @33
    @5
    @25
    wph
    @33
    @2
    wps
    wph
    @33
    grpidinvlem3.2
    biimpi
    ad2antrl
    ad2antrr
    @32
    @29
    vx
    @11
    cX
    @14
    @11
    wceq
    #
    @31
    @28
    @14
    @11
    @14
    @11
    cU
    cG
    oveq2
    @35
    id
    eqeq12d
    rspcva
    syl2anc
    adantr
    @27
    @11
    @11
    cG
    co
    @11
    wceq
    #
    @28
    cU
    wceq
    #
    @27
    @0
    @25
    @5
    wa
    #
    wa
    #
    cU
    @7
    cG
    co
    #
    @7
    wceq
    #
    @9
    wa
    @36
    @26
    @39
    @9
    @2
    @5
    @25
    @39
    @3
    @0
    @5
    @25
    @39
    @1
    @25
    @5
    @0
    @39
    @38
    @0
    pm3.22
    an31s
    adantllr
    adantllr
    adantr
    @26
    @41
    @9
    @3
    @5
    @25
    @41
    @2
    @3
    @25
    @41
    @5
    wph
    @25
    @41
    wps
    wph
    @33
    @25
    @41
    grpidinvlem3.2
    @32
    @41
    vx
    @7
    cX
    @14
    @7
    wceq
    #
    @31
    @40
    @14
    @7
    @14
    @7
    cU
    cG
    oveq2
    @42
    id
    eqeq12d
    rspccva
    sylanb
    adantlr
    adantlr
    adantlll
    anim1i
    cA
    cU
    cG
    cX
    @7
    grpfo.1
    grpoidinvlem2
    syl2anc
    @26
    @36
    @37
    wi
    #
    @9
    @4
    @5
    @25
    @43
    @2
    wph
    wps
    @5
    @25
    wa
    #
    @43
    wi
    @2
    wph
    @44
    wps
    @43
    @2
    wph
    @44
    wps
    @43
    wi
    @2
    wph
    @44
    wa
    wa
    #
    @30
    wps
    @43
    @0
    @44
    @30
    @1
    wph
    @0
    @5
    @25
    @30
    @34
    3expb
    #
    ad2ant2rl
    @30
    wps
    wa
    vw
    cv
    #
    @11
    cG
    co
    #
    cU
    wceq
    #
    vw
    cX
    wrex
    #
    @45
    @43
    wps
    @30
    @47
    @14
    cG
    co
    #
    cU
    wceq
    #
    vw
    cX
    wrex
    #
    vx
    cX
    wral
    #
    @50
    wps
    @23
    @54
    grpidinvlem3.3
    @22
    @53
    vx
    cX
    @21
    @52
    vz
    vw
    cX
    @19
    @47
    wceq
    @20
    @51
    cU
    @19
    @47
    @14
    cG
    oveq1
    eqeq1d
    cbvrexv
    ralbii
    bitri
    @53
    @50
    vx
    @11
    cX
    @35
    @52
    @49
    vw
    cX
    @35
    @51
    @48
    cU
    @14
    @11
    @47
    cG
    oveq2
    eqeq1d
    rexbidv
    rspcva
    sylan2b
    @45
    @49
    @43
    vw
    cX
    @45
    @47
    cX
    wcel
    #
    @49
    @36
    @37
    @45
    @55
    wa
    @0
    @55
    @30
    wa
    wa
    #
    @49
    @36
    wa
    @37
    @45
    @55
    @56
    @0
    @44
    @55
    @56
    wi
    #
    @1
    wph
    @0
    @44
    @30
    @57
    @46
    @0
    @30
    wa
    @55
    @56
    @0
    @55
    @30
    @56
    @0
    @55
    wa
    @30
    wa
    @56
    @0
    @55
    @30
    anass
    biimpi
    an32s
    ex
    syldan
    ad2ant2rl
    imp
    @11
    cU
    cG
    cX
    @47
    grpfo.1
    grpoidinvlem1
    sylan
    exp43
    rexlimdv
    syl5
    mpand
    exp32
    com34
    imp32
    impl
    adantr
    mpd
    eqtr3d
    ex
    ancld
    reximdva
    mpd
end
