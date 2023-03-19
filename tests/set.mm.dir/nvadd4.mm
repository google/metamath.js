include "cnv.mm"
include "wcel.mm"
include "cablo.mm"
include "wa.mm"
include "co.mm"
include "wceq.mm"
include "nvablo.mm"
include "bafval.mm"
include "ablo4.mm"
include "syl3an1.mm"

theorem nvadd4
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cU: class U
  let cG: class G
  let cX: class X
  assume nvgcl.1: |- X = ( BaseSet ` U )
  assume nvgcl.2: |- G = ( +v ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X ) /\ ( C e. X /\ D e. X ) ) -> ( ( A G B ) G ( C G D ) ) = ( ( A G C ) G ( B G D ) ) )

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
    wa
    cC
    cX
    wcel
    cD
    cX
    wcel
    wa
    cA
    cB
    cG
    co
    cC
    cD
    cG
    co
    cG
    co
    cA
    cC
    cG
    co
    cB
    cD
    cG
    co
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
    cD
    cG
    cX
    cU
    cG
    cX
    nvgcl.1
    nvgcl.2
    bafval
    ablo4
    syl3an1
end
