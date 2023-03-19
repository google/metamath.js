include "cnv.mm"
include "wcel.mm"
include "cablo.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "nvablo.mm"
include "bafval.mm"
include "ablo32.mm"
include "sylan.mm"

theorem nvadd32
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cG: class G
  let cX: class X
  assume nvgcl.1: |- X = ( BaseSet ` U )
  assume nvgcl.2: |- G = ( +v ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) G C ) = ( ( A G C ) G B ) )

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
    cG
    co
    cA
    cC
    cG
    co
    cB
    cG
    co
    wceq
    cU
    cG
    nvgcl.2
    nvablo
    cA
    cB
    cC
    cG
    cX
    cU
    cG
    cX
    nvgcl.1
    nvgcl.2
    bafval
    ablo32
    sylan
end
