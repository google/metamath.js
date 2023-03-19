include "chlo.mm"
include "wcel.mm"
include "ccphlo.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "caddc.mm"
include "cmul.mm"
include "wceq.mm"
include "hlph.mm"
include "phpar.mm"
include "syl3an1.mm"

theorem hlpar
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  assume hlpar.1: |- X = ( BaseSet ` U )
  assume hlpar.2: |- G = ( +v ` U )
  assume hlpar.4: |- S = ( .sOLD ` U )
  assume hlpar.6: |- N = ( normCV ` U )


  assert |- ( ( U e. CHilOLD /\ A e. X /\ B e. X ) -> ( ( ( N ` ( A G B ) ) ^ 2 ) + ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) = ( 2 x. ( ( ( N ` A ) ^ 2 ) + ( ( N ` B ) ^ 2 ) ) ) )

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
    c1
    cneg
    cB
    cS
    co
    cG
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
    cS
    cU
    cG
    cN
    cX
    hlpar.1
    hlpar.2
    hlpar.4
    hlpar.6
    phpar
    syl3an1
end
