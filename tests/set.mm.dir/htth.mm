include "chlo.mm"
include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wi.mm"
include "caddc.mm"
include "cmul.mm"
include "cop.mm"
include "cabs.mm"
include "cif.mm"
include "clno.mm"
include "cdip.mm"
include "cba.mm"
include "cblo.mm"
include "oveq12.mm"
include "anidms.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "fveq2.mm"
include "oveqd.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "cmpt.mm"
include "cnmcv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "crab.mm"
include "cima.mm"
include "eqid.mm"
include "cnchl.mm"
include "elimel.mm"
include "simpl.mm"
include "simpr.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq2d.mm"
include "oveq2.mm"
include "cbvral2v.mm"
include "sylib.mm"
include "cbvmptv.mm"
include "mpteq2dv.mm"
include "breq1d.mm"
include "cbvrabv.mm"
include "imaeq2i.mm"
include "htthlem.mm"
include "dedth.mm"
include "3impib.mm"

theorem htth
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cP: class P
  let cT: class T
  let cU: class U
  let cL: class L
  let cX: class X
  let vw: setvar w
  let cF: class F
  let vz: setvar z
  let cK: class K
  let cN: class N
  let cW: class W
  let wph: wff ph
  let vu: setvar u
  let vv: setvar v
  assume htth.1: |- X = ( BaseSet ` U )
  assume htth.2: |- P = ( .iOLD ` U )
  assume htth.3: |- L = ( U LnOp U )
  assume htth.4: |- B = ( U BLnOp U )

  disjoint x y
  disjoint T x
  disjoint T y
  disjoint U x
  disjoint U y
  disjoint X x
  disjoint X y
  disjoint w y
  disjoint F w
  disjoint F y
  disjoint w x
  disjoint w z
  disjoint K w
  disjoint x z
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint K z
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint N z
  disjoint P w
  disjoint P z
  disjoint W w
  disjoint W x
  disjoint W y
  disjoint W z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint T u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint T v
  disjoint T w
  disjoint T z
  disjoint U u
  disjoint U v
  disjoint U w
  disjoint U z
  disjoint X w
  disjoint X z
  assert |- ( ( U e. CHilOLD /\ T e. L /\ A. x e. X A. y e. X ( x P ( T ` y ) ) = ( ( T ` x ) P y ) ) -> T e. B )

  proof
    cU
    chlo
    wcel
    #
    cT
    cL
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cT
    cfv
    #
    cP
    co
    #
    @2
    cT
    cfv
    #
    @3
    cP
    co
    #
    wceq
    #
    vy
    cX
    wral
    #
    vx
    cX
    wral
    #
    cT
    cB
    wcel
    #
    @0
    @1
    @10
    wa
    #
    @11
    wi
    cT
    @0
    cU
    caddc
    cmul
    cop
    cabs
    cop
    #
    cif
    #
    @14
    clno
    co
    #
    wcel
    #
    @2
    @4
    @14
    cdip
    cfv
    #
    co
    #
    @6
    @3
    @17
    co
    #
    wceq
    #
    vy
    @14
    cba
    cfv
    #
    wral
    #
    vx
    @21
    wral
    #
    wa
    #
    cT
    @14
    @14
    cblo
    co
    #
    wcel
    #
    wi
    cU
    @13
    cU
    @14
    wceq
    #
    @12
    @24
    @11
    @26
    @27
    @1
    @16
    @10
    @23
    @27
    cL
    @15
    cT
    @27
    cL
    cU
    cU
    clno
    co
    #
    @15
    htth.3
    @27
    @28
    @15
    wceq
    cU
    @14
    cU
    @14
    clno
    oveq12
    anidms
    syl5eq
    eleq2d
    @27
    @9
    @22
    vx
    cX
    @21
    @27
    cX
    cU
    cba
    cfv
    @21
    htth.1
    cU
    @14
    cba
    fveq2
    syl5eq
    #
    @27
    @8
    @20
    vy
    cX
    @21
    @29
    @27
    @5
    @18
    @7
    @19
    @27
    cP
    @17
    @2
    @4
    @27
    cP
    cU
    cdip
    cfv
    @17
    htth.2
    cU
    @14
    cdip
    fveq2
    syl5eq
    #
    oveqd
    @27
    cP
    @17
    @6
    @3
    @30
    oveqd
    eqeq12d
    raleqbidv
    raleqbidv
    anbi12d
    @27
    cB
    @25
    cT
    @27
    cB
    cU
    cU
    cblo
    co
    #
    @25
    htth.4
    @27
    @31
    @25
    wceq
    cU
    @14
    cU
    @14
    cblo
    oveq12
    anidms
    syl5eq
    eleq2d
    imbi12d
    @24
    vu
    vv
    vz
    vw
    @25
    @17
    cT
    @14
    vx
    @21
    vy
    @21
    @3
    @6
    @17
    co
    #
    cmpt
    #
    cmpt
    #
    @34
    @2
    @14
    cnmcv
    cfv
    #
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    @21
    crab
    #
    cima
    @15
    @35
    @13
    @21
    @21
    eqid
    @17
    eqid
    @15
    eqid
    @25
    eqid
    @35
    eqid
    cU
    @13
    chlo
    @13
    @13
    eqid
    #
    cnchl
    elimel
    @39
    @16
    @23
    simpl
    @24
    @23
    vu
    cv
    #
    vv
    cv
    #
    cT
    cfv
    #
    @17
    co
    #
    @40
    cT
    cfv
    #
    @41
    @17
    co
    #
    wceq
    #
    vv
    @21
    wral
    vu
    @21
    wral
    @16
    @23
    simpr
    @20
    @46
    @40
    @4
    @17
    co
    #
    @44
    @3
    @17
    co
    #
    wceq
    vx
    vy
    vu
    vv
    @21
    @21
    @2
    @40
    wceq
    #
    @18
    @47
    @19
    @48
    @2
    @40
    @4
    @17
    oveq1
    @49
    @6
    @44
    @3
    @17
    @2
    @40
    cT
    fveq2
    oveq1d
    eqeq12d
    @3
    @41
    wceq
    #
    @47
    @43
    @48
    @45
    @50
    @4
    @42
    @40
    @17
    @3
    @41
    cT
    fveq2
    oveq2d
    @3
    @41
    @44
    @17
    oveq2
    eqeq12d
    cbvral2v
    sylib
    vx
    vz
    @21
    @33
    vw
    @21
    vw
    cv
    #
    vz
    cv
    #
    cT
    cfv
    #
    @17
    co
    #
    cmpt
    #
    @2
    @52
    wceq
    #
    @33
    vw
    @21
    @51
    @6
    @17
    co
    #
    cmpt
    @55
    vy
    vw
    @21
    @32
    @57
    @3
    @51
    @6
    @17
    oveq1
    cbvmptv
    @56
    vw
    @21
    @57
    @54
    @56
    @6
    @53
    @51
    @17
    @2
    @52
    cT
    fveq2
    oveq2d
    mpteq2dv
    syl5eq
    cbvmptv
    @38
    @52
    @35
    cfv
    #
    c1
    cle
    wbr
    #
    vz
    @21
    crab
    @34
    @37
    @59
    vx
    vz
    @21
    @56
    @36
    @58
    c1
    cle
    @2
    @52
    @35
    fveq2
    breq1d
    cbvrabv
    imaeq2i
    htthlem
    dedth
    3impib
end
