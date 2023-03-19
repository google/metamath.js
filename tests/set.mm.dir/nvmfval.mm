include "cnv.mm"
include "wcel.mm"
include "cv.mm"
include "cgn.mm"
include "cfv.mm"
include "co.mm"
include "cmpt2.mm"
include "c1.mm"
include "cneg.mm"
include "cgr.mm"
include "wceq.mm"
include "nvgrp.mm"
include "bafval.mm"
include "eqid.mm"
include "vsfval.mm"
include "grpodivfval.mm"
include "syl.mm"
include "w3a.mm"
include "nvinv.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "mpt2eq3dva.mm"
include "eqtr4d.mm"

theorem nvmfval
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cU: class U
  let cG: class G
  let cM: class M
  let cX: class X
  assume nvmval.1: |- X = ( BaseSet ` U )
  assume nvmval.2: |- G = ( +v ` U )
  assume nvmval.4: |- S = ( .sOLD ` U )
  assume nvmval.3: |- M = ( -v ` U )

  disjoint x y
  disjoint G x
  disjoint G y
  disjoint U x
  disjoint U y
  disjoint X x
  disjoint X y
  assert |- ( U e. NrmCVec -> M = ( x e. X , y e. X |-> ( x G ( -u 1 S y ) ) ) )

  proof
    cU
    cnv
    wcel
    #
    cM
    vx
    vy
    cX
    cX
    vx
    cv
    #
    vy
    cv
    #
    cG
    cgn
    cfv
    #
    cfv
    #
    cG
    co
    #
    cmpt2
    #
    vx
    vy
    cX
    cX
    @1
    c1
    cneg
    @2
    cS
    co
    #
    cG
    co
    #
    cmpt2
    @0
    cG
    cgr
    wcel
    cM
    @6
    wceq
    cU
    cG
    nvmval.2
    nvgrp
    vx
    vy
    cM
    cG
    @3
    cX
    cU
    cG
    cX
    nvmval.1
    nvmval.2
    bafval
    @3
    eqid
    #
    cU
    cG
    cM
    nvmval.2
    nvmval.3
    vsfval
    grpodivfval
    syl
    @0
    vx
    vy
    cX
    cX
    @8
    @5
    @0
    @1
    cX
    wcel
    #
    @2
    cX
    wcel
    #
    w3a
    @7
    @4
    @1
    cG
    @0
    @11
    @7
    @4
    wceq
    @10
    @2
    cS
    cU
    cG
    @3
    cX
    nvmval.1
    nvmval.2
    nvmval.4
    @9
    nvinv
    3adant2
    oveq2d
    mpt2eq3dva
    eqtr4d
end
