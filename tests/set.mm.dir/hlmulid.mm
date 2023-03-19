include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "c1.mm"
include "co.mm"
include "wceq.mm"
include "hlnv.mm"
include "nvsid.mm"
include "sylan.mm"

theorem hlmulid
  let cA: class A
  let cS: class S
  let cU: class U
  let cX: class X
  assume hlmulf.1: |- X = ( BaseSet ` U )
  assume hlmulf.4: |- S = ( .sOLD ` U )


  assert |- ( ( U e. CHilOLD /\ A e. X ) -> ( 1 S A ) = A )

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
    c1
    cA
    cS
    co
    cA
    wceq
    cU
    hlnv
    cA
    cS
    cU
    cX
    hlmulf.1
    hlmulf.4
    nvsid
    sylan
end
