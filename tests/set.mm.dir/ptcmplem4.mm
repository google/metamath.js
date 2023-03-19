include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "cuni.mm"
include "cdif.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "wex.mm"
include "ptcmplem3.mm"
include "wrex.mm"
include "cixp.mm"
include "simprl.mm"
include "eldifi.mm"
include "ralimi.mm"
include "wceq.mm"
include "fveq2.mm"
include "unieqd.mm"
include "eleq12d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "ad2antll.mm"
include "vex.mm"
include "elixp.mm"
include "sylanbrc.mm"
include "syl6eleqr.mm"
include "adantr.mm"
include "eleqtrd.mm"
include "eluni2.mm"
include "sylib.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "wi.mm"
include "simplrr.mm"
include "simprr.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "eqid.mm"
include "mptpreima.mm"
include "elrab2.mm"
include "simprbi.mm"
include "syl.mm"
include "crab.mm"
include "simplrl.mm"
include "eqeltrrd.mm"
include "rabid.mm"
include "elunii.mm"
include "syl2anc.mm"
include "rexlimdvaa.mm"
include "expr.mm"
include "ralimdva.mm"
include "ex.mm"
include "com23.mm"
include "impr.mm"
include "imp.mm"
include "cab.mm"
include "crn.mm"
include "wss.mm"
include "sselda.mm"
include "adantrr.mm"
include "rnmpt2.mm"
include "syl6eleq.mm"
include "abid.mm"
include "rexim.mm"
include "sylc.mm"
include "rexlimddv.mm"
include "wn.mm"
include "eldifn.mm"
include "ralnex.mm"
include "pm2.65da.mm"
include "nexdv.mm"
include "pm2.65i.mm"

theorem ptcmplem4
  let wph: wff ph
  let vz: setvar z
  let vw: setvar w
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cU: class U
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cK: class K
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vt: setvar t
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume ptcmp.1: |- S = ( k e. A , u e. ( F ` k ) |-> ( `' ( w e. X |-> ( w ` k ) ) " u ) )
  assume ptcmp.2: |- X = X_ n e. A U. ( F ` n )
  assume ptcmp.3: |- ( ph -> A e. V )
  assume ptcmp.4: |- ( ph -> F : A --> Comp )
  assume ptcmp.5: |- ( ph -> X e. ( UFL i^i dom card ) )
  assume ptcmplem2.5: |- ( ph -> U C_ ran S )
  assume ptcmplem2.6: |- ( ph -> X = U. U )
  assume ptcmplem2.7: |- ( ph -> -. E. z e. ( ~P U i^i Fin ) X = U. z )
  assume ptcmplem3.8: |- K = { u e. ( F ` k ) | ( `' ( w e. X |-> ( w ` k ) ) " u ) e. U }

  disjoint k n
  disjoint k u
  disjoint k w
  disjoint k z
  disjoint A k
  disjoint n u
  disjoint n w
  disjoint n z
  disjoint A n
  disjoint u w
  disjoint u z
  disjoint A u
  disjoint w z
  disjoint A w
  disjoint A z
  disjoint K u
  disjoint S k
  disjoint S n
  disjoint S u
  disjoint S z
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint U k
  disjoint U u
  disjoint U z
  disjoint V k
  disjoint V n
  disjoint V u
  disjoint V w
  disjoint V z
  disjoint F k
  disjoint F n
  disjoint F u
  disjoint F w
  disjoint F z
  disjoint X k
  disjoint X n
  disjoint X u
  disjoint X w
  disjoint X z
  disjoint f g
  disjoint f k
  disjoint f m
  disjoint f n
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint f w
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint A f
  disjoint g k
  disjoint g m
  disjoint g n
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint A g
  disjoint k m
  disjoint k t
  disjoint k v
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m t
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n t
  disjoint n v
  disjoint n x
  disjoint n y
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint K f
  disjoint K g
  disjoint K t
  disjoint K v
  disjoint K x
  disjoint K y
  disjoint S v
  disjoint S y
  disjoint f ph
  disjoint g ph
  disjoint m ph
  disjoint ph t
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint U t
  disjoint U v
  disjoint U x
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint F f
  disjoint F g
  disjoint F m
  disjoint F t
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint X f
  disjoint X g
  disjoint X m
  disjoint X t
  disjoint X v
  disjoint X x
  disjoint X y
  assert |- -. ph

  proof
    wph
    vf
    cv
    #
    cA
    wfn
    #
    vk
    cv
    #
    @0
    cfv
    #
    @2
    cF
    cfv
    #
    cuni
    #
    cK
    cuni
    #
    cdif
    wcel
    #
    vk
    cA
    wral
    #
    wa
    #
    vf
    wex
    wph
    vz
    vw
    vu
    cA
    cS
    cU
    vf
    vk
    vn
    cF
    cK
    cV
    cX
    ptcmp.1
    ptcmp.2
    ptcmp.3
    ptcmp.4
    ptcmp.5
    ptcmplem2.5
    ptcmplem2.6
    ptcmplem2.7
    ptcmplem3.8
    ptcmplem3
    wph
    @9
    vf
    wph
    @9
    @3
    @6
    wcel
    #
    vk
    cA
    wrex
    #
    wph
    @9
    wa
    #
    @0
    vv
    cv
    #
    wcel
    #
    @11
    vv
    cU
    @12
    @0
    cU
    cuni
    #
    wcel
    @14
    vv
    cU
    wrex
    @12
    @0
    cX
    @15
    @12
    @0
    vn
    cA
    vn
    cv
    #
    cF
    cfv
    #
    cuni
    #
    cixp
    #
    cX
    @12
    @1
    @16
    @0
    cfv
    #
    @18
    wcel
    #
    vn
    cA
    wral
    #
    @0
    @19
    wcel
    wph
    @1
    @8
    simprl
    @8
    @22
    wph
    @1
    @8
    @3
    @5
    wcel
    #
    vk
    cA
    wral
    @22
    @7
    @23
    vk
    cA
    @3
    @5
    @6
    eldifi
    ralimi
    @21
    @23
    vn
    vk
    cA
    @16
    @2
    wceq
    #
    @20
    @3
    @18
    @5
    @16
    @2
    @0
    fveq2
    @24
    @17
    @4
    @16
    @2
    cF
    fveq2
    unieqd
    eleq12d
    cbvralv
    sylibr
    ad2antll
    vn
    cA
    @18
    @0
    vf
    vex
    elixp
    sylanbrc
    ptcmp.2
    syl6eleqr
    wph
    cX
    @15
    wceq
    @9
    ptcmplem2.6
    adantr
    eleqtrd
    vv
    @0
    cU
    eluni2
    sylib
    @12
    @13
    cU
    wcel
    #
    @14
    wa
    #
    wa
    #
    @13
    vw
    cX
    @2
    vw
    cv
    #
    cfv
    #
    cmpt
    #
    ccnv
    vu
    cv
    #
    cima
    #
    wceq
    #
    vu
    @4
    wrex
    #
    @10
    wi
    #
    vk
    cA
    wral
    #
    @34
    vk
    cA
    wrex
    #
    @11
    @12
    @26
    @36
    wph
    @1
    @8
    @26
    @36
    wi
    wph
    @1
    wa
    #
    @26
    @8
    @36
    @38
    @26
    @8
    @36
    wi
    @38
    @26
    wa
    #
    @7
    @35
    vk
    cA
    @39
    @2
    cA
    wcel
    #
    @7
    @35
    @39
    @40
    @7
    wa
    #
    wa
    #
    @33
    @10
    vu
    @4
    @42
    @31
    @4
    wcel
    #
    @33
    wa
    #
    wa
    #
    @3
    @31
    wcel
    #
    @31
    cK
    wcel
    @10
    @45
    @0
    @32
    wcel
    #
    @46
    @45
    @0
    @13
    @32
    @42
    @14
    @44
    @38
    @25
    @14
    @41
    simplrr
    adantr
    @42
    @43
    @33
    simprr
    #
    eleqtrd
    @47
    @0
    cX
    wcel
    @46
    @29
    @31
    wcel
    @46
    vw
    @0
    cX
    @32
    @28
    @0
    wceq
    @29
    @3
    @31
    @2
    @28
    @0
    fveq1
    eleq1d
    vw
    cX
    @29
    @31
    @30
    @30
    eqid
    mptpreima
    elrab2
    simprbi
    syl
    @45
    @31
    @32
    cU
    wcel
    #
    vu
    @4
    crab
    #
    cK
    @45
    @43
    @49
    @31
    @50
    wcel
    @42
    @43
    @33
    simprl
    @45
    @13
    @32
    cU
    @48
    @42
    @25
    @44
    @38
    @25
    @14
    @41
    simplrl
    adantr
    eqeltrrd
    @49
    vu
    @4
    rabid
    sylanbrc
    ptcmplem3.8
    syl6eleqr
    @3
    @31
    cK
    elunii
    syl2anc
    rexlimdvaa
    expr
    ralimdva
    ex
    com23
    impr
    imp
    @27
    @13
    @37
    vv
    cab
    #
    wcel
    @37
    @27
    @13
    cS
    crn
    #
    @51
    @12
    @25
    @13
    @52
    wcel
    @14
    @12
    cU
    @52
    @13
    wph
    cU
    @52
    wss
    @9
    ptcmplem2.5
    adantr
    sselda
    adantrr
    vk
    vu
    vv
    cA
    @4
    @32
    cS
    ptcmp.1
    rnmpt2
    syl6eleq
    @37
    vv
    abid
    sylib
    @34
    @10
    vk
    cA
    rexim
    sylc
    rexlimddv
    @12
    @10
    wn
    #
    vk
    cA
    wral
    #
    @11
    wn
    @8
    @54
    wph
    @1
    @7
    @53
    vk
    cA
    @3
    @5
    @6
    eldifn
    ralimi
    ad2antll
    @10
    vk
    cA
    ralnex
    sylib
    pm2.65da
    nexdv
    pm2.65i
end
