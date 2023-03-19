include "co.mm"
include "wceq.mm"
include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cgs.mm"
include "cfv.mm"
include "vsfval.mm"
include "eqtr4i.mm"
include "oveqi.mm"
include "a1i.mm"

theorem nvm
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  assume nvm.1: |- X = ( BaseSet ` U )
  assume nvm.2: |- G = ( +v ` U )
  assume nvm.3: |- M = ( -v ` U )
  assume nvm.6: |- N = ( /g ` G )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A M B ) = ( A N B ) )

  proof
    cA
    cB
    cM
    co
    cA
    cB
    cN
    co
    wceq
    cU
    cnv
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    w3a
    cM
    cN
    cA
    cB
    cM
    cG
    cgs
    cfv
    cN
    cU
    cG
    cM
    nvm.2
    nvm.3
    vsfval
    nvm.6
    eqtr4i
    oveqi
    a1i
end
