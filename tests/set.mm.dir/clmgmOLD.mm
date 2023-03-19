include "cmagm.mm"
include "wcel.mm"
include "co.mm"
include "wi.mm"
include "cxp.mm"
include "wf.mm"
include "ismgmOLD.mm"
include "fovrn.mm"
include "3exp.mm"
include "syl6bi.mm"
include "pm2.43i.mm"
include "3imp.mm"

theorem clmgmOLD
  let cA: class A
  let cB: class B
  let cG: class G
  let cX: class X
  assume clmgmOLD.1: |- X = dom dom G


  assert |- ( ( G e. Magma /\ A e. X /\ B e. X ) -> ( A G B ) e. X )

  proof
    cG
    cmagm
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    cA
    cB
    cG
    co
    cX
    wcel
    #
    @0
    @1
    @2
    @3
    wi
    wi
    #
    @0
    @0
    cX
    cX
    cxp
    cX
    cG
    wf
    #
    @4
    cmagm
    cG
    cX
    clmgmOLD.1
    ismgmOLD
    @5
    @1
    @2
    @3
    cA
    cB
    cX
    cX
    cX
    cG
    fovrn
    3exp
    syl6bi
    pm2.43i
    3imp
end
