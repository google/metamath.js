include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "co.mm"
include "wceq.mm"
include "hlnv.mm"
include "nvcom.mm"
include "syl3an1.mm"

theorem hlcom
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cX: class X
  assume hladdf.1: |- X = ( BaseSet ` U )
  assume hladdf.2: |- G = ( +v ` U )


  assert |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) -> ( A G B ) = ( B G A ) )

  proof
    cU
    chlo
    wcel
    cU
    cnv
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
    hlnv
    cA
    cB
    cU
    cG
    cX
    hladdf.1
    hladdf.2
    nvcom
    syl3an1
end
