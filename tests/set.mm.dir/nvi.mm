include "cnv.mm"
include "wcel.mm"
include "cop.mm"
include "cvc.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wi.mm"
include "co.mm"
include "cabs.mm"
include "cmul.mm"
include "cc.mm"
include "wral.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cgi.mm"
include "c1st.mm"
include "eqid.mm"
include "nvop2.mm"
include "nvvop.mm"
include "opeq1d.mm"
include "eqtrd.mm"
include "id.mm"
include "eqeltrrd.mm"
include "bafval.mm"
include "isnv.mm"
include "sylib.mm"
include "0vfval.mm"
include "eqeq2d.mm"
include "imbi2d.mm"
include "3anbi1d.mm"
include "ralbidv.mm"
include "3anbi3d.mm"
include "mpbird.mm"

theorem nvi
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  assume nvi.1: |- X = ( BaseSet ` U )
  assume nvi.2: |- G = ( +v ` U )
  assume nvi.4: |- S = ( .sOLD ` U )
  assume nvi.5: |- Z = ( 0vec ` U )
  assume nvi.6: |- N = ( normCV ` U )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint N x
  disjoint N y
  disjoint U x
  disjoint S x
  disjoint S y
  disjoint X x
  disjoint X y
  assert |- ( U e. NrmCVec -> ( <. G , S >. e. CVecOLD /\ N : X --> RR /\ A. x e. X ( ( ( N ` x ) = 0 -> x = Z ) /\ A. y e. CC ( N ` ( y S x ) ) = ( ( abs ` y ) x. ( N ` x ) ) /\ A. y e. X ( N ` ( x G y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) )

  proof
    cU
    cnv
    wcel
    #
    cG
    cS
    cop
    #
    cvc
    wcel
    #
    cX
    cr
    cN
    wf
    #
    vx
    cv
    #
    cN
    cfv
    #
    cc0
    wceq
    #
    @4
    cZ
    wceq
    #
    wi
    #
    vy
    cv
    #
    @4
    cS
    co
    cN
    cfv
    @9
    cabs
    cfv
    @5
    cmul
    co
    wceq
    vy
    cc
    wral
    #
    @4
    @9
    cG
    co
    cN
    cfv
    @5
    @9
    cN
    cfv
    caddc
    co
    cle
    wbr
    vy
    cX
    wral
    #
    w3a
    #
    vx
    cX
    wral
    #
    w3a
    @2
    @3
    @6
    @4
    cG
    cgi
    cfv
    #
    wceq
    #
    wi
    #
    @10
    @11
    w3a
    #
    vx
    cX
    wral
    #
    w3a
    #
    @0
    @1
    cN
    cop
    #
    cnv
    wcel
    @19
    @0
    cU
    @20
    cnv
    @0
    cU
    cU
    c1st
    cfv
    #
    cN
    cop
    @20
    cU
    cN
    @21
    @21
    eqid
    #
    nvi.6
    nvop2
    @0
    @21
    @1
    cN
    cS
    cU
    cG
    @21
    @22
    nvi.2
    nvi.4
    nvvop
    opeq1d
    eqtrd
    @0
    id
    eqeltrrd
    vx
    vy
    cS
    cG
    cN
    cX
    @14
    cU
    cG
    cX
    nvi.1
    nvi.2
    bafval
    @14
    eqid
    isnv
    sylib
    @0
    @13
    @18
    @2
    @3
    @0
    @12
    @17
    vx
    cX
    @0
    @8
    @16
    @10
    @11
    @0
    @7
    @15
    @6
    @0
    cZ
    @14
    @4
    cU
    cG
    cnv
    cZ
    nvi.2
    nvi.5
    0vfval
    eqeq2d
    imbi2d
    3anbi1d
    ralbidv
    3anbi3d
    mpbird
end
