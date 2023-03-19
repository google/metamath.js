include "crn.mm"
include "csn.mm"
include "cun.mm"
include "cuni.mm"
include "wceq.mm"
include "cpt.mm"
include "cfv.mm"
include "cfi.mm"
include "ctg.mm"
include "cv.mm"
include "wfn.mm"
include "wcel.mm"
include "wral.mm"
include "cdif.mm"
include "cfn.mm"
include "wrex.mm"
include "w3a.mm"
include "cixp.mm"
include "wa.mm"
include "wex.mm"
include "cab.mm"
include "ccmp.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "eqid.mm"
include "ptval.mm"
include "syl2anc.mm"
include "cmpt.mm"
include "ccnv.mm"
include "cima.mm"
include "cmpt2.mm"
include "ctop.mm"
include "wss.mm"
include "cmptop.mm"
include "ssriv.mm"
include "fss.mm"
include "sylancl.mm"
include "ptbasfi.mm"
include "uncom.mm"
include "rneqi.mm"
include "uneq2i.mm"
include "eqtri.mm"
include "fveq2i.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "unieqd.mm"
include "ctb.mm"
include "fibas.mm"
include "unitg.mm"
include "ax-mp.mm"
include "syl6eq.mm"
include "ptuni.mm"
include "syl5eq.mm"
include "cvv.mm"
include "cpw.mm"
include "cufl.mm"
include "ccrd.mm"
include "cdm.mm"
include "cin.mm"
include "pwexg.mm"
include "cxp.mm"
include "ciun.mm"
include "crab.mm"
include "mptpreima.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "wb.mm"
include "adantr.mm"
include "elpw2g.mm"
include "mpbiri.mm"
include "ralrimivva.mm"
include "fmpt2x.mm"
include "sylib.mm"
include "frn.mm"
include "ssexd.mm"
include "snex.mm"
include "unexg.mm"
include "fiuni.mm"
include "3eqtr4d.mm"
include "jca.mm"

theorem ptcmplem1
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
  assert |- ( ph -> ( X = U. ( ran S u. { X } ) /\ ( Xt_ ` F ) = ( topGen ` ( fi ` ( ran S u. { X } ) ) ) ) )

  proof
    wph
    cX
    cS
    crn
    #
    cX
    csn
    #
    cun
    #
    cuni
    #
    wceq
    cF
    cpt
    cfv
    #
    @2
    cfi
    cfv
    #
    ctg
    cfv
    #
    wceq
    wph
    @4
    cuni
    #
    @5
    cuni
    #
    cX
    @3
    wph
    @7
    @6
    cuni
    #
    @8
    wph
    @4
    @6
    wph
    @4
    vg
    cv
    #
    cA
    wfn
    vy
    cv
    #
    @10
    cfv
    #
    @11
    cF
    cfv
    #
    wcel
    vy
    cA
    wral
    @12
    @13
    cuni
    wceq
    vy
    cA
    vz
    cv
    cdif
    wral
    vz
    cfn
    wrex
    w3a
    vx
    cv
    #
    vy
    cA
    @12
    cixp
    wceq
    wa
    vg
    wex
    vx
    cab
    #
    ctg
    cfv
    #
    @6
    wph
    cA
    cV
    wcel
    #
    cF
    cA
    wfn
    #
    @4
    @16
    wceq
    ptcmp.3
    wph
    cA
    ccmp
    cF
    wf
    #
    @18
    ptcmp.4
    cA
    ccmp
    cF
    ffn
    syl
    vx
    vy
    vz
    cA
    @15
    vg
    cF
    cV
    @15
    eqid
    #
    ptval
    syl2anc
    wph
    @15
    @5
    ctg
    wph
    @15
    @1
    vk
    vu
    cA
    vk
    cv
    #
    cF
    cfv
    #
    vw
    cX
    @21
    vw
    cv
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
    cmpt2
    #
    crn
    #
    cun
    #
    cfi
    cfv
    #
    @5
    wph
    @17
    cA
    ctop
    cF
    wf
    #
    @15
    @30
    wceq
    ptcmp.3
    wph
    @19
    ccmp
    ctop
    wss
    @31
    ptcmp.4
    vx
    ccmp
    ctop
    @14
    cmptop
    ssriv
    cA
    ccmp
    ctop
    cF
    fss
    sylancl
    #
    vx
    vy
    vz
    vw
    vu
    cA
    @15
    vg
    vk
    vn
    cF
    cV
    cX
    @20
    ptcmp.2
    ptbasfi
    syl2anc
    @2
    @29
    cfi
    @2
    @1
    @0
    cun
    @29
    @0
    @1
    uncom
    @0
    @28
    @1
    cS
    @27
    ptcmp.1
    rneqi
    uneq2i
    eqtri
    fveq2i
    syl6eqr
    fveq2d
    eqtrd
    #
    unieqd
    @5
    ctb
    wcel
    @9
    @8
    wceq
    @2
    fibas
    @5
    ctb
    unitg
    ax-mp
    syl6eq
    wph
    cX
    vn
    cA
    vn
    cv
    cF
    cfv
    cuni
    cixp
    #
    @7
    ptcmp.2
    wph
    @17
    @31
    @34
    @7
    wceq
    ptcmp.3
    @32
    vn
    cA
    cF
    @4
    cV
    @4
    eqid
    ptuni
    syl2anc
    syl5eq
    wph
    @2
    cvv
    wcel
    #
    @3
    @8
    wceq
    wph
    @0
    cvv
    wcel
    @1
    cvv
    wcel
    @35
    wph
    @0
    cX
    cpw
    #
    cvv
    wph
    cX
    cufl
    ccrd
    cdm
    cin
    #
    wcel
    #
    @36
    cvv
    wcel
    ptcmp.5
    cX
    @37
    pwexg
    syl
    wph
    vk
    cA
    @21
    csn
    @22
    cxp
    ciun
    #
    @36
    cS
    wf
    #
    @0
    @36
    wss
    wph
    @26
    @36
    wcel
    #
    vu
    @22
    wral
    vk
    cA
    wral
    @40
    wph
    @41
    vk
    vu
    cA
    @22
    wph
    @21
    cA
    wcel
    @25
    @22
    wcel
    wa
    #
    wa
    #
    @41
    @26
    cX
    wss
    #
    @26
    @23
    @25
    wcel
    #
    vw
    cX
    crab
    cX
    vw
    cX
    @23
    @25
    @24
    @24
    eqid
    mptpreima
    @45
    vw
    cX
    ssrab2
    eqsstri
    @43
    @38
    @41
    @44
    wb
    wph
    @38
    @42
    ptcmp.5
    adantr
    @26
    cX
    @37
    elpw2g
    syl
    mpbiri
    ralrimivva
    vk
    vu
    cA
    @22
    @26
    @36
    cS
    ptcmp.1
    fmpt2x
    sylib
    @39
    @36
    cS
    frn
    syl
    ssexd
    cX
    snex
    @0
    @1
    cvv
    cvv
    unexg
    sylancl
    @2
    cvv
    fiuni
    syl
    3eqtr4d
    @33
    jca
end
