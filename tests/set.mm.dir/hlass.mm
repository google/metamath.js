include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "hlnv.mm"
include "nvass.mm"
include "sylan.mm"

theorem hlass
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cG: class G
  let cX: class X
  assume hladdf.1: |- X = ( BaseSet ` U )
  assume hladdf.2: |- G = ( +v ` U )


  assert |- ( ( U e. CHilOLD /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) G C ) = ( A G ( B G C ) ) )

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
    cB
    cC
    cG
    co
    cG
    co
    wceq
    cU
    hlnv
    cA
    cB
    cC
    cU
    cG
    cX
    hladdf.1
    hladdf.2
    nvass
    sylan
end
