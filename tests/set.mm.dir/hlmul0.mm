include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "cc0.mm"
include "co.mm"
include "wceq.mm"
include "hlnv.mm"
include "nv0.mm"
include "sylan.mm"

theorem hlmul0
  let cA: class A
  let cS: class S
  let cU: class U
  let cX: class X
  let cZ: class Z
  assume hlmul0.1: |- X = ( BaseSet ` U )
  assume hlmul0.4: |- S = ( .sOLD ` U )
  assume hlmul0.5: |- Z = ( 0vec ` U )


  assert |- ( ( U e. CHilOLD /\ A e. X ) -> ( 0 S A ) = Z )

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
    cc0
    cA
    cS
    co
    cZ
    wceq
    cU
    hlnv
    cA
    cS
    cU
    cX
    cZ
    hlmul0.1
    hlmul0.4
    hlmul0.5
    nv0
    sylan
end
