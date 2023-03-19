include "cnv.mm"
include "wcel.mm"
include "cablo.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "nvablo.mm"
include "bafval.mm"
include "vsfval.mm"
include "ablomuldiv.mm"
include "sylan.mm"

theorem nvaddsub
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cG: class G
  let cM: class M
  let cX: class X
  assume nvpncan2.1: |- X = ( BaseSet ` U )
  assume nvpncan2.2: |- G = ( +v ` U )
  assume nvpncan2.3: |- M = ( -v ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) M C ) = ( ( A M C ) G B ) )

  proof
    cU
    cnv
    wcel
    cG
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
    cG
    co
    cC
    cM
    co
    cA
    cC
    cM
    co
    cB
    cG
    co
    wceq
    cU
    cG
    nvpncan2.2
    nvablo
    cA
    cB
    cC
    cM
    cG
    cX
    cU
    cG
    cX
    nvpncan2.1
    nvpncan2.2
    bafval
    cU
    cG
    cM
    nvpncan2.2
    nvpncan2.3
    vsfval
    ablomuldiv
    sylan
end
