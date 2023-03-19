include "co.mm"
include "cn.mm"
include "cxrs.mm"
include "cv.mm"
include "ccom.mm"
include "cgsu.mm"
include "cmpt.mm"
include "crn.mm"
include "ciun.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "imasdsval.mm"
include "wceq.mm"
include "wcel.mm"
include "cxp.mm"
include "cres.mm"
include "coeq1i.mm"
include "c1.mm"
include "cfz.mm"
include "cmap.mm"
include "wf.mm"
include "wss.mm"
include "cfv.mm"
include "c1st.mm"
include "c2nd.mm"
include "caddc.mm"
include "cmin.mm"
include "wral.mm"
include "w3a.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "sseli.mm"
include "elmapi.mm"
include "frn.mm"
include "cores.mm"
include "4syl.mm"
include "syl5eq.mm"
include "oveq2d.mm"
include "mpteq2ia.mm"
include "rneqi.mm"
include "a1i.mm"
include "iuneq2i.mm"
include "infeq1i.mm"
include "syl6eqr.mm"

theorem imasdsval2
  let wph: wff ph
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cT: class T
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
  assume imasds.u: |- T = ( E |` ( V X. V ) )

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
  assert |- ( ph -> ( X D Y ) = inf ( U_ n e. NN ran ( g e. S |-> ( RR*s gsum ( T o. g ) ) ) , RR* , < ) )

  proof
    wph
    cX
    cY
    cD
    co
    vn
    cn
    vg
    cS
    cxrs
    cE
    vg
    cv
    #
    ccom
    #
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
    cxrs
    cT
    @0
    ccom
    #
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
    wph
    cB
    cD
    cR
    cS
    cU
    vg
    vh
    vi
    vn
    cE
    cF
    cV
    cX
    cY
    cZ
    imasbas.u
    imasbas.v
    imasbas.f
    imasbas.r
    imasds.e
    imasds.d
    imasdsval.x
    imasdsval.y
    imasdsval.s
    imasdsval
    cxr
    @10
    @5
    clt
    vn
    cn
    @9
    @4
    @9
    @4
    wceq
    vn
    cv
    #
    cn
    wcel
    @8
    @3
    vg
    cS
    @7
    @2
    @0
    cS
    wcel
    #
    @6
    @1
    cxrs
    cgsu
    @12
    @6
    cE
    cV
    cV
    cxp
    #
    cres
    #
    @0
    ccom
    #
    @1
    cT
    @14
    @0
    imasds.u
    coeq1i
    @12
    @0
    @13
    c1
    @11
    cfz
    co
    #
    cmap
    co
    #
    wcel
    @16
    @13
    @0
    wf
    @0
    crn
    @13
    wss
    @15
    @1
    wceq
    cS
    @17
    @0
    cS
    c1
    vh
    cv
    #
    cfv
    c1st
    cfv
    cF
    cfv
    cX
    wceq
    @11
    @18
    cfv
    c2nd
    cfv
    cF
    cfv
    cY
    wceq
    vi
    cv
    #
    @18
    cfv
    c2nd
    cfv
    cF
    cfv
    @19
    c1
    caddc
    co
    @18
    cfv
    c1st
    cfv
    cF
    cfv
    wceq
    vi
    c1
    @11
    c1
    cmin
    co
    cfz
    co
    wral
    w3a
    #
    vh
    @17
    crab
    @17
    imasdsval.s
    @20
    vh
    @17
    ssrab2
    eqsstri
    sseli
    @0
    @13
    @16
    elmapi
    @16
    @13
    @0
    frn
    cE
    @0
    @13
    cores
    4syl
    syl5eq
    oveq2d
    mpteq2ia
    rneqi
    a1i
    iuneq2i
    infeq1i
    syl6eqr
end
