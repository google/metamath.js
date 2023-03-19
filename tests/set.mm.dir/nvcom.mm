include "cnv.mm"
include "wcel.mm"
include "cablo.mm"
include "co.mm"
include "wceq.mm"
include "nvablo.mm"
include "bafval.mm"
include "ablocom.mm"
include "syl3an1.mm"

theorem nvcom
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cX: class X
  assume nvgcl.1: |- X = ( BaseSet ` U )
  assume nvgcl.2: |- G = ( +v ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A G B ) = ( B G A ) )

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
    cA
    cB
    cG
    co
    cB
    cA
    cG
    co
    wceq
    cU
    cG
    nvgcl.2
    nvablo
    cA
    cB
    cG
    cX
    cU
    cG
    cX
    nvgcl.1
    nvgcl.2
    bafval
    ablocom
    syl3an1
end
