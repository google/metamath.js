include "cnv.mm"
include "wcel.mm"
include "cgr.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "nvgrp.mm"
include "bafval.mm"
include "grporcan.mm"
include "sylan.mm"

theorem nvrcan
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cG: class G
  let cX: class X
  assume nvgcl.1: |- X = ( BaseSet ` U )
  assume nvgcl.2: |- G = ( +v ` U )


  assert |- ( ( U e. NrmCVec /\ ( A e. X /\ B e. X /\ C e. X ) ) -> ( ( A G C ) = ( B G C ) <-> A = B ) )

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
    cC
    cG
    co
    cB
    cC
    cG
    co
    wceq
    cA
    cB
    wceq
    wb
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
    grporcan
    sylan
end
