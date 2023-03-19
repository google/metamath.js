include "chlo.mm"
include "wcel.mm"
include "cnv.mm"
include "co.mm"
include "wceq.mm"
include "hlnv.mm"
include "nv0rid.mm"
include "sylan.mm"

theorem hladdid
  let cA: class A
  let cU: class U
  let cG: class G
  let cX: class X
  let cZ: class Z
  assume hladdid.1: |- X = ( BaseSet ` U )
  assume hladdid.2: |- G = ( +v ` U )
  assume hladdid.5: |- Z = ( 0vec ` U )


  assert |- ( ( U e. CHilOLD /\ A e. X ) -> ( A G Z ) = A )

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
    cA
    cZ
    cG
    co
    cA
    wceq
    cU
    hlnv
    cA
    cU
    cG
    cX
    cZ
    hladdid.1
    hladdid.2
    hladdid.5
    nv0rid
    sylan
end
