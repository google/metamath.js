include "cnv.mm"
include "wcel.mm"
include "wa.mm"
include "cnmoo.mm"
include "co.mm"
include "cmap.mm"
include "cv.mm"
include "cfv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt.mm"
include "cba.mm"
include "cnmcv.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "rexeqbidv.mm"
include "abbidv.mm"
include "supeq1d.mm"
include "mpteq12dv.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "df-nmoo.mm"
include "ovex.mm"
include "mptex.mm"
include "ovmpt2.mm"
include "syl5eq.mm"

theorem nmoofval
  let vx: setvar x
  let vz: setvar z
  let vt: setvar t
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vu: setvar u
  let vw: setvar w
  let cT: class T
  assume nmoofval.1: |- X = ( BaseSet ` U )
  assume nmoofval.2: |- Y = ( BaseSet ` W )
  assume nmoofval.3: |- L = ( normCV ` U )
  assume nmoofval.4: |- M = ( normCV ` W )
  assume nmoofval.6: |- N = ( U normOpOLD W )

  disjoint t x
  disjoint t z
  disjoint U t
  disjoint x z
  disjoint U x
  disjoint U z
  disjoint W t
  disjoint W x
  disjoint W z
  disjoint X t
  disjoint X z
  disjoint Y t
  disjoint Y x
  disjoint L t
  disjoint M t
  disjoint t u
  disjoint t w
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint U u
  disjoint w x
  disjoint w z
  disjoint U w
  disjoint W u
  disjoint W w
  disjoint X u
  disjoint X w
  disjoint Y u
  disjoint Y w
  disjoint L u
  disjoint L w
  disjoint M u
  disjoint M w
  disjoint T t
  disjoint T x
  disjoint T z
  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec ) -> N = ( t e. ( Y ^m X ) |-> sup ( { x | E. z e. X ( ( L ` z ) <_ 1 /\ x = ( M ` ( t ` z ) ) ) } , RR* , < ) ) )

  proof
    cU
    cnv
    wcel
    cW
    cnv
    wcel
    wa
    cN
    cU
    cW
    cnmoo
    co
    vt
    cY
    cX
    cmap
    co
    #
    vz
    cv
    #
    cL
    cfv
    #
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @1
    vt
    cv
    cfv
    #
    cM
    cfv
    #
    wceq
    #
    wa
    #
    vz
    cX
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cmpt
    #
    nmoofval.6
    vu
    vw
    cU
    cW
    cnv
    cnv
    vt
    vw
    cv
    #
    cba
    cfv
    #
    vu
    cv
    #
    cba
    cfv
    #
    cmap
    co
    #
    @1
    @15
    cnmcv
    cfv
    #
    cfv
    #
    c1
    cle
    wbr
    #
    @4
    @5
    @13
    cnmcv
    cfv
    #
    cfv
    #
    wceq
    #
    wa
    #
    vz
    @16
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cmpt
    @12
    cnmoo
    vt
    @14
    cX
    cmap
    co
    #
    @3
    @23
    wa
    #
    vz
    cX
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    #
    cmpt
    @15
    cU
    wceq
    #
    vt
    @17
    @27
    @28
    @32
    @33
    @16
    cX
    @14
    cmap
    @33
    @16
    cU
    cba
    cfv
    cX
    @15
    cU
    cba
    fveq2
    nmoofval.1
    syl6eqr
    #
    oveq2d
    @33
    cxr
    @26
    @31
    clt
    @33
    @25
    @30
    vx
    @33
    @24
    @29
    vz
    @16
    cX
    @34
    @33
    @20
    @3
    @23
    @33
    @19
    @2
    c1
    cle
    @33
    @1
    @18
    cL
    @33
    @18
    cU
    cnmcv
    cfv
    cL
    @15
    cU
    cnmcv
    fveq2
    nmoofval.3
    syl6eqr
    fveq1d
    breq1d
    anbi1d
    rexeqbidv
    abbidv
    supeq1d
    mpteq12dv
    @13
    cW
    wceq
    #
    vt
    @28
    @32
    @0
    @11
    @35
    @14
    cY
    cX
    cmap
    @35
    @14
    cW
    cba
    cfv
    cY
    @13
    cW
    cba
    fveq2
    nmoofval.2
    syl6eqr
    oveq1d
    @35
    cxr
    @31
    @10
    clt
    @35
    @30
    @9
    vx
    @35
    @29
    @8
    vz
    cX
    @35
    @23
    @7
    @3
    @35
    @22
    @6
    @4
    @35
    @5
    @21
    cM
    @35
    @21
    cW
    cnmcv
    cfv
    cM
    @13
    cW
    cnmcv
    fveq2
    nmoofval.4
    syl6eqr
    fveq1d
    eqeq2d
    anbi2d
    rexbidv
    abbidv
    supeq1d
    mpteq12dv
    vx
    vz
    vw
    vu
    vt
    df-nmoo
    vt
    @0
    @11
    cY
    cX
    cmap
    ovex
    mptex
    ovmpt2
    syl5eq
end
