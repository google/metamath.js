include "cn.mm"
include "c1.mm"
include "cv.mm"
include "cfv.mm"
include "c1st.mm"
include "wceq.mm"
include "c2nd.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "cfz.mm"
include "wral.mm"
include "w3a.mm"
include "cxp.mm"
include "cmap.mm"
include "crab.mm"
include "cxrs.mm"
include "ccom.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "cvv.mm"
include "imasds.mm"
include "wa.mm"
include "wcel.mm"
include "simplrl.mm"
include "eqeq2d.mm"
include "simplrr.mm"
include "3anbi12d.mm"
include "rabbidv.mm"
include "syl6eqr.mm"
include "mpteq1d.mm"
include "rneqd.mm"
include "iuneq2dv.mm"
include "infeq1d.mm"
include "xrltso.mm"
include "infex.mm"
include "a1i.mm"
include "ovmpt2d.mm"

theorem imasdsval
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cU: class U
  let vg: setvar g
  let vh: setvar h
  let vi: setvar i
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cV: class V
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vp: setvar p
  let vq: setvar q
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cK: class K
  assume imasbas.u: |- ( ph -> U = ( F "s R ) )
  assume imasbas.v: |- ( ph -> V = ( Base ` R ) )
  assume imasbas.f: |- ( ph -> F : V -onto-> B )
  assume imasbas.r: |- ( ph -> R e. Z )
  assume imasds.e: |- E = ( dist ` R )
  assume imasds.d: |- D = ( dist ` U )
  assume imasdsval.x: |- ( ph -> X e. B )
  assume imasdsval.y: |- ( ph -> Y e. B )
  assume imasdsval.s: |- S = { h e. ( ( V X. V ) ^m ( 1 ... n ) ) | ( ( F ` ( 1st ` ( h ` 1 ) ) ) = X /\ ( F ` ( 2nd ` ( h ` n ) ) ) = Y /\ A. i e. ( 1 ... ( n - 1 ) ) ( F ` ( 2nd ` ( h ` i ) ) ) = ( F ` ( 1st ` ( h ` ( i + 1 ) ) ) ) ) }

  disjoint g h
  disjoint g i
  disjoint g n
  disjoint F g
  disjoint h i
  disjoint h n
  disjoint F h
  disjoint i n
  disjoint F i
  disjoint F n
  disjoint R g
  disjoint R h
  disjoint R i
  disjoint R n
  disjoint g ph
  disjoint h ph
  disjoint i ph
  disjoint n ph
  disjoint X h
  disjoint X n
  disjoint S g
  disjoint V g
  disjoint V h
  disjoint Y h
  disjoint Y n
  disjoint g p
  disjoint g q
  disjoint g u
  disjoint g v
  disjoint g w
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint h p
  disjoint h q
  disjoint h u
  disjoint h v
  disjoint h w
  disjoint h x
  disjoint h y
  disjoint h z
  disjoint i p
  disjoint i q
  disjoint i u
  disjoint i v
  disjoint i w
  disjoint i x
  disjoint i y
  disjoint i z
  disjoint n p
  disjoint n q
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint p q
  disjoint p u
  disjoint p v
  disjoint p w
  disjoint p x
  disjoint p y
  disjoint p z
  disjoint F p
  disjoint q u
  disjoint q v
  disjoint q w
  disjoint q x
  disjoint q y
  disjoint q z
  disjoint F q
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint R p
  disjoint R q
  disjoint R u
  disjoint R v
  disjoint R w
  disjoint R x
  disjoint R y
  disjoint R z
  disjoint U x
  disjoint B x
  disjoint B y
  disjoint E x
  disjoint E y
  disjoint p ph
  disjoint ph q
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint X y
  disjoint K p
  disjoint K x
  disjoint S x
  disjoint S y
  disjoint V p
  disjoint V q
  disjoint V w
  disjoint V z
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( X D Y ) = inf ( U_ n e. NN ran ( g e. S |-> ( RR*s gsum ( E o. g ) ) ) , RR* , < ) )

  proof
    wph
    vx
    vy
    cX
    cY
    cB
    cB
    vn
    cn
    vg
    c1
    vh
    cv
    #
    cfv
    c1st
    cfv
    cF
    cfv
    #
    vx
    cv
    #
    wceq
    #
    vn
    cv
    #
    @0
    cfv
    c2nd
    cfv
    cF
    cfv
    #
    vy
    cv
    #
    wceq
    #
    vi
    cv
    #
    @0
    cfv
    c2nd
    cfv
    cF
    cfv
    @8
    c1
    caddc
    co
    @0
    cfv
    c1st
    cfv
    cF
    cfv
    wceq
    vi
    c1
    @4
    c1
    cmin
    co
    cfz
    co
    wral
    #
    w3a
    #
    vh
    cV
    cV
    cxp
    c1
    @4
    cfz
    co
    cmap
    co
    #
    crab
    #
    cxrs
    cE
    vg
    cv
    ccom
    cgsu
    co
    #
    cmpt
    #
    crn
    #
    ciun
    #
    cxr
    clt
    cinf
    vn
    cn
    vg
    cS
    @13
    cmpt
    #
    crn
    #
    ciun
    #
    cxr
    clt
    cinf
    #
    cD
    cvv
    wph
    vx
    vy
    cB
    cD
    cR
    cU
    vg
    vh
    vi
    vn
    cE
    cF
    cV
    cZ
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    imasds.e
    imasds.d
    imasds
    wph
    @2
    cX
    wceq
    #
    @6
    cY
    wceq
    #
    wa
    wa
    #
    cxr
    @16
    @19
    clt
    @23
    vn
    cn
    @15
    @18
    @23
    @4
    cn
    wcel
    #
    wa
    #
    @14
    @17
    @25
    vg
    @12
    cS
    @13
    @25
    @12
    @1
    cX
    wceq
    #
    @5
    cY
    wceq
    #
    @9
    w3a
    #
    vh
    @11
    crab
    cS
    @25
    @10
    @28
    vh
    @11
    @25
    @3
    @26
    @7
    @27
    @9
    @25
    @2
    cX
    @1
    wph
    @21
    @22
    @24
    simplrl
    eqeq2d
    @25
    @6
    cY
    @5
    wph
    @21
    @22
    @24
    simplrr
    eqeq2d
    3anbi12d
    rabbidv
    imasdsval.s
    syl6eqr
    mpteq1d
    rneqd
    iuneq2dv
    infeq1d
    imasdsval.x
    imasdsval.y
    @20
    cvv
    wcel
    wph
    cxr
    @19
    clt
    xrltso
    infex
    a1i
    ovmpt2d
end
