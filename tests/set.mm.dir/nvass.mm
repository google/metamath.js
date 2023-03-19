include "cnv.mm"
include "wcel.mm"
include "cgr.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "nvgrp.mm"
include "bafval.mm"
include "grpoass.mm"
include "sylan.mm"

theorem nvass
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cG: class G
  let cX: class X
  assume nvgcl.1: |- X = ( BaseSet ` U )
  assume nvgcl.2: |- G = ( +v ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G B ) G C ) = ( A G ( B G C ) ) )

  proof
    cU
    cnv
    wcel
    cG
    cgr
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
    cG
    nvgcl.2
    nvgrp
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
    grpoass
    sylan
end
