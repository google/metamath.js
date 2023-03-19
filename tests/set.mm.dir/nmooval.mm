include "cnv.mm"
include "wcel.mm"
include "wf.mm"
include "cfv.mm"
include "cv.mm"
include "c1.mm"
include "cle.mm"
include "wbr.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmap.mm"
include "co.mm"
include "cba.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "elmap.mm"
include "cmpt.mm"
include "nmoofval.mm"
include "fveq1d.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "supeq1d.mm"
include "eqid.mm"
include "xrltso.mm"
include "supex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "sylan2br.mm"
include "3impa.mm"

theorem nmooval
  let vx: setvar x
  let vz: setvar z
  let cT: class T
  let cU: class U
  let cL: class L
  let cM: class M
  let cN: class N
  let cW: class W
  let cX: class X
  let cY: class Y
  let vt: setvar t
  let vu: setvar u
  let vw: setvar w
  assume nmoofval.1: |- X = ( BaseSet ` U )
  assume nmoofval.2: |- Y = ( BaseSet ` W )
  assume nmoofval.3: |- L = ( normCV ` U )
  assume nmoofval.4: |- M = ( normCV ` W )
  assume nmoofval.6: |- N = ( U normOpOLD W )

  disjoint x z
  disjoint U x
  disjoint U z
  disjoint W x
  disjoint W z
  disjoint X z
  disjoint Y x
  disjoint T x
  disjoint T z
  disjoint t u
  disjoint t w
  disjoint t x
  disjoint t z
  disjoint U t
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint U u
  disjoint w x
  disjoint w z
  disjoint U w
  disjoint W t
  disjoint W u
  disjoint W w
  disjoint X t
  disjoint X u
  disjoint X w
  disjoint Y t
  disjoint Y u
  disjoint Y w
  disjoint L t
  disjoint L u
  disjoint L w
  disjoint M t
  disjoint M u
  disjoint M w
  disjoint T t
  assert |- ( ( U e. NrmCVec /\ W e. NrmCVec /\ T : X --> Y ) -> ( N ` T ) = sup ( { x | E. z e. X ( ( L ` z ) <_ 1 /\ x = ( M ` ( T ` z ) ) ) } , RR* , < ) )

  proof
    cU
    cnv
    wcel
    #
    cW
    cnv
    wcel
    #
    cX
    cY
    cT
    wf
    #
    cT
    cN
    cfv
    #
    vz
    cv
    #
    cL
    cfv
    c1
    cle
    wbr
    #
    vx
    cv
    #
    @4
    cT
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
    wceq
    #
    @2
    @0
    @1
    wa
    #
    cT
    cY
    cX
    cmap
    co
    #
    wcel
    #
    @14
    cY
    cX
    cT
    cY
    cW
    cba
    cfv
    cvv
    nmoofval.2
    cW
    cba
    fvex
    eqeltri
    cX
    cU
    cba
    cfv
    cvv
    nmoofval.1
    cU
    cba
    fvex
    eqeltri
    elmap
    @15
    @17
    @3
    cT
    vt
    @16
    @5
    @6
    @4
    vt
    cv
    #
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
    cfv
    @13
    @15
    cT
    cN
    @26
    vx
    vz
    vt
    cU
    cL
    cM
    cN
    cW
    cX
    cY
    nmoofval.1
    nmoofval.2
    nmoofval.3
    nmoofval.4
    nmoofval.6
    nmoofval
    fveq1d
    vt
    cT
    @25
    @13
    @16
    @26
    @18
    cT
    wceq
    #
    cxr
    @24
    @12
    clt
    @27
    @23
    @11
    vx
    @27
    @22
    @10
    vz
    cX
    @27
    @21
    @9
    @5
    @27
    @20
    @8
    @6
    @27
    @19
    @7
    cM
    @4
    @18
    cT
    fveq1
    fveq2d
    eqeq2d
    anbi2d
    rexbidv
    abbidv
    supeq1d
    @26
    eqid
    cxr
    @12
    clt
    xrltso
    supex
    fvmpt
    sylan9eq
    sylan2br
    3impa
end
