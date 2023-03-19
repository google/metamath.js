include "crn.mm"
include "csn.mm"
include "cun.mm"
include "cpt.mm"
include "cfv.mm"
include "cufl.mm"
include "ccrd.mm"
include "cdm.mm"
include "cin.mm"
include "inss1.mm"
include "sseldi.mm"
include "cuni.mm"
include "wceq.mm"
include "cfi.mm"
include "ctg.mm"
include "ptcmplem1.mm"
include "simpld.mm"
include "simprd.mm"
include "cv.mm"
include "wss.mm"
include "cpw.mm"
include "cfn.mm"
include "wrex.mm"
include "wa.mm"
include "wcel.mm"
include "wi.mm"
include "elpwi.mm"
include "wn.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "crab.mm"
include "ad2antrr.mm"
include "ccmp.mm"
include "wf.mm"
include "simplrl.mm"
include "simplrr.mm"
include "simpr.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "cbvrabv.mm"
include "ptcmplem4.mm"
include "iman.mm"
include "mpbir.mm"
include "expr.mm"
include "sylan2.mm"
include "adantlr.mm"
include "selpw.mm"
include "cdif.mm"
include "eldif.mm"
include "elpwunsn.mm"
include "sylbir.mm"
include "sylanbr.mm"
include "adantll.mm"
include "snssi.mm"
include "adantl.mm"
include "snfi.mm"
include "a1i.mm"
include "elfpw.mm"
include "sylanbrc.mm"
include "unisng.mm"
include "eqcomd.mm"
include "unieq.mm"
include "eqeq2d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "a1d.mm"
include "syldan.mm"
include "pm2.61dan.mm"
include "impr.mm"
include "alexsub.mm"

theorem ptcmplem5
  let wph: wff ph
  let vw: setvar w
  let vu: setvar u
  let cA: class A
  let cS: class S
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cV: class V
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vt: setvar t
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  let cU: class U
  assume ptcmp.1: |- S = ( k e. A , u e. ( F ` k ) |-> ( `' ( w e. X |-> ( w ` k ) ) " u ) )
  assume ptcmp.2: |- X = X_ n e. A U. ( F ` n )
  assume ptcmp.3: |- ( ph -> A e. V )
  assume ptcmp.4: |- ( ph -> F : A --> Comp )
  assume ptcmp.5: |- ( ph -> X e. ( UFL i^i dom card ) )

  disjoint k n
  disjoint k u
  disjoint k w
  disjoint A k
  disjoint n u
  disjoint n w
  disjoint A n
  disjoint u w
  disjoint A u
  disjoint A w
  disjoint S k
  disjoint S n
  disjoint S u
  disjoint k ph
  disjoint n ph
  disjoint ph u
  disjoint V k
  disjoint V n
  disjoint V u
  disjoint V w
  disjoint F k
  disjoint F n
  disjoint F u
  disjoint F w
  disjoint X k
  disjoint X n
  disjoint X u
  disjoint X w
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
  disjoint k z
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
  disjoint n z
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
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint K f
  disjoint K g
  disjoint K t
  disjoint K u
  disjoint K v
  disjoint K x
  disjoint K y
  disjoint S v
  disjoint S y
  disjoint S z
  disjoint f ph
  disjoint g ph
  disjoint m ph
  disjoint ph t
  disjoint ph v
  disjoint ph x
  disjoint ph y
  disjoint U k
  disjoint U t
  disjoint U u
  disjoint U v
  disjoint U x
  disjoint U z
  disjoint V g
  disjoint V x
  disjoint V y
  disjoint V z
  disjoint F f
  disjoint F g
  disjoint F m
  disjoint F t
  disjoint F v
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint X f
  disjoint X g
  disjoint X m
  disjoint X t
  disjoint X v
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint ph z
  assert |- ( ph -> ( Xt_ ` F ) e. Comp )

  proof
    wph
    vy
    vz
    cS
    crn
    #
    cX
    csn
    #
    cun
    #
    cF
    cpt
    cfv
    #
    cX
    wph
    cufl
    ccrd
    cdm
    #
    cin
    #
    cufl
    cX
    cufl
    @4
    inss1
    ptcmp.5
    sseldi
    wph
    cX
    @2
    cuni
    wceq
    #
    @3
    @2
    cfi
    cfv
    ctg
    cfv
    wceq
    #
    wph
    vw
    vu
    cA
    cS
    vk
    vn
    cF
    cV
    cX
    ptcmp.1
    ptcmp.2
    ptcmp.3
    ptcmp.4
    ptcmp.5
    ptcmplem1
    #
    simpld
    wph
    @6
    @7
    @8
    simprd
    wph
    vy
    cv
    #
    @2
    wss
    #
    cX
    @9
    cuni
    wceq
    #
    cX
    vz
    cv
    #
    cuni
    #
    wceq
    #
    vz
    @9
    cpw
    cfn
    cin
    #
    wrex
    #
    wph
    @10
    wa
    #
    @9
    @0
    cpw
    #
    wcel
    #
    @11
    @16
    wi
    #
    wph
    @19
    @20
    @10
    @19
    wph
    @9
    @0
    wss
    #
    @20
    @9
    @0
    elpwi
    wph
    @21
    @11
    @16
    wph
    @21
    @11
    wa
    #
    wa
    #
    @16
    wi
    @23
    @16
    wn
    #
    wa
    #
    wn
    @25
    vz
    vw
    vu
    cA
    cS
    @9
    vk
    vn
    cF
    vw
    cX
    vk
    cv
    #
    vw
    cv
    cfv
    cmpt
    ccnv
    #
    @12
    cima
    #
    @9
    wcel
    #
    vz
    @26
    cF
    cfv
    #
    crab
    cV
    cX
    ptcmp.1
    ptcmp.2
    wph
    cA
    cV
    wcel
    @22
    @24
    ptcmp.3
    ad2antrr
    wph
    cA
    ccmp
    cF
    wf
    @22
    @24
    ptcmp.4
    ad2antrr
    wph
    cX
    @5
    wcel
    @22
    @24
    ptcmp.5
    ad2antrr
    wph
    @21
    @11
    @24
    simplrl
    wph
    @21
    @11
    @24
    simplrr
    @23
    @24
    simpr
    @29
    @27
    vu
    cv
    #
    cima
    #
    @9
    wcel
    vz
    vu
    @30
    @12
    @31
    wceq
    @28
    @32
    @9
    @12
    @31
    @27
    imaeq2
    eleq1d
    cbvrabv
    ptcmplem4
    @23
    @16
    iman
    mpbir
    expr
    sylan2
    adantlr
    @17
    @19
    wn
    #
    cX
    @9
    wcel
    #
    @20
    @10
    @33
    @34
    wph
    @10
    @9
    @2
    cpw
    #
    wcel
    #
    @33
    @34
    vy
    @2
    selpw
    @36
    @33
    wa
    @9
    @35
    @18
    cdif
    wcel
    @34
    @9
    @35
    @18
    eldif
    @9
    @0
    cX
    elpwunsn
    sylbir
    sylanbr
    adantll
    @17
    @34
    wa
    #
    @16
    @11
    @37
    @1
    @15
    wcel
    #
    cX
    @1
    cuni
    #
    wceq
    #
    @16
    @37
    @1
    @9
    wss
    #
    @1
    cfn
    wcel
    #
    @38
    @34
    @41
    @17
    cX
    @9
    snssi
    adantl
    @42
    @37
    cX
    snfi
    a1i
    @1
    @9
    elfpw
    sylanbrc
    @34
    @40
    @17
    @34
    @39
    cX
    cX
    @9
    unisng
    eqcomd
    adantl
    @14
    @40
    vz
    @1
    @15
    @12
    @1
    wceq
    @13
    @39
    cX
    @12
    @1
    unieq
    eqeq2d
    rspcev
    syl2anc
    a1d
    syldan
    pm2.61dan
    impr
    alexsub
end
