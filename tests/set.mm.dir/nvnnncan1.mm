include "cnv.mm"
include "wcel.mm"
include "cpv.mm"
include "cfv.mm"
include "cablo.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "eqid.mm"
include "nvablo.mm"
include "bafval.mm"
include "vsfval.mm"
include "ablonnncan1.mm"
include "sylan.mm"

theorem nvnnncan1
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cM: class M
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume nvmf.1: |- X = ( BaseSet ` U )
  assume nvmf.3: |- M = ( -v ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A M B ) M ( A M C ) ) = ( C M B ) )

  proof
    cU
    cnv
    wcel
    cU
    cpv
    cfv
    #
    cablo
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    cC
    cX
    wcel
    w3a
    cA
    cB
    cM
    co
    cA
    cC
    cM
    co
    cM
    co
    cC
    cB
    cM
    co
    wceq
    cU
    @0
    @0
    eqid
    #
    nvablo
    cA
    cB
    cC
    cM
    @0
    cX
    cU
    @0
    cX
    nvmf.1
    @1
    bafval
    cU
    @0
    cM
    @1
    nvmf.3
    vsfval
    ablonnncan1
    sylan
end
