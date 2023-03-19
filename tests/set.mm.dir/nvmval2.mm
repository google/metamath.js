include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "nvmval.mm"
include "wceq.mm"
include "cc.mm"
include "neg1cn.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "3adant2.mm"
include "nvcom.mm"
include "syld3an3.mm"
include "eqtrd.mm"

theorem nvmval2
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


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A M B ) = ( ( -u 1 S B ) G A ) )

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
    cA
    cB
    cM
    co
    cA
    c1
    cneg
    #
    cB
    cS
    co
    #
    cG
    co
    #
    @4
    cA
    cG
    co
    #
    cA
    cB
    cS
    cU
    cG
    cM
    cX
    nvmval.1
    nvmval.2
    nvmval.4
    nvmval.3
    nvmval
    @0
    @1
    @2
    @4
    cX
    wcel
    #
    @5
    @6
    wceq
    @0
    @2
    @7
    @1
    @0
    @3
    cc
    wcel
    @2
    @7
    neg1cn
    @3
    cB
    cS
    cU
    cX
    nvmval.1
    nvmval.4
    nvscl
    mp3an2
    3adant2
    cA
    @4
    cU
    cG
    cX
    nvmval.1
    nvmval.2
    nvcom
    syld3an3
    eqtrd
end
