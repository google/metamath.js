include "chlo.mm"
include "wcel.mm"
include "ccphlo.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "hlph.mm"
include "phpar2.mm"
include "syl3an1.mm"

theorem hlpar2
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  assume hlpar2.1: |- X = ( BaseSet ` U )
  assume hlpar2.2: |- G = ( +v ` U )
  assume hlpar2.3: |- M = ( -v ` U )
  assume hlpar2.6: |- N = ( normCV ` U )


  assert |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) -> ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A M B ) ) ^ 2 ) ) = ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) )

  proof
    cU
    chlo
    wcel
    cU
    ccphlo
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
    cN
    cfv
    c2
    cexp
    co
    cA
    cB
    cM
    co
    cN
    cfv
    c2
    cexp
    co
    caddc
    co
    c2
    cA
    cN
    cfv
    c2
    cexp
    co
    cB
    cN
    cfv
    c2
    cexp
    co
    caddc
    co
    cmul
    co
    wceq
    cU
    hlph
    cA
    cB
    cU
    cG
    cM
    cN
    cX
    hlpar2.1
    hlpar2.2
    hlpar2.3
    hlpar2.6
    phpar2
    syl3an1
end
