include "cnv.mm"
include "wcel.mm"
include "cgr.mm"
include "co.mm"
include "nvgrp.mm"
include "bafval.mm"
include "grpocl.mm"
include "syl3an1.mm"

theorem nvgcl
  let cA: class A
  let cB: class B
  let cU: class U
  let cG: class G
  let cX: class X
  assume nvgcl.1: |- X = ( BaseSet ` U )
  assume nvgcl.2: |- G = ( +v ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( A G B ) e. X )

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
    cA
    cB
    cG
    co
    cX
    wcel
    cU
    cG
    nvgcl.2
    nvgrp
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
    grpocl
    syl3an1
end
