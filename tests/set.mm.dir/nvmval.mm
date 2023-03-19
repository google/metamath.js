include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cgs.mm"
include "cfv.mm"
include "co.mm"
include "cgn.mm"
include "c1.mm"
include "cneg.mm"
include "cgr.mm"
include "wceq.mm"
include "nvgrp.mm"
include "bafval.mm"
include "eqid.mm"
include "grpodivval.mm"
include "syl3an1.mm"
include "nvm.mm"
include "nvinv.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "3eqtr4d.mm"

theorem nvmval
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cG: class G
  let cM: class M
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume nvmval.1: |- X = ( BaseSet ` U )
  assume nvmval.2: |- G = ( +v ` U )
  assume nvmval.4: |- S = ( .sOLD ` U )
  assume nvmval.3: |- M = ( -v ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A M B ) = ( A G ( -u 1 S B ) ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    cG
    cgs
    cfv
    #
    co
    #
    cA
    cB
    cG
    cgn
    cfv
    #
    cfv
    #
    cG
    co
    #
    cA
    cB
    cM
    co
    cA
    c1
    cneg
    cB
    cS
    co
    #
    cG
    co
    @0
    cG
    cgr
    wcel
    @1
    @2
    @5
    @8
    wceq
    cU
    cG
    nvmval.2
    nvgrp
    cA
    cB
    @4
    cG
    @6
    cX
    cU
    cG
    cX
    nvmval.1
    nvmval.2
    bafval
    @6
    eqid
    #
    @4
    eqid
    #
    grpodivval
    syl3an1
    cA
    cB
    cU
    cG
    cM
    @4
    cX
    nvmval.1
    nvmval.2
    nvmval.3
    @11
    nvm
    @3
    @9
    @7
    cA
    cG
    @0
    @2
    @9
    @7
    wceq
    @1
    cB
    cS
    cU
    cG
    @6
    cX
    nvmval.1
    nvmval.2
    nvmval.4
    @10
    nvinv
    3adant2
    oveq2d
    3eqtr4d
end
