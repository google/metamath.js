include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "csm.mm"
include "co.mm"
include "wceq.mm"
include "hvmulcom.mm"
include "mp3an.mm"

theorem hvmulcomi
  let cA: class A
  let cB: class B
  let cC: class C
  assume hvmulcom.1: |- A e. CC
  assume hvmulcom.2: |- B e. CC
  assume hvmulcom.3: |- C e. ~H


  assert |- ( A .h ( B .h C ) ) = ( B .h ( A .h C ) )

  proof
    cA
    cc
    wcel
    cB
    cc
    wcel
    cC
    chil
    wcel
    cA
    cB
    cC
    csm
    co
    csm
    co
    cB
    cA
    cC
    csm
    co
    csm
    co
    wceq
    hvmulcom.1
    hvmulcom.2
    hvmulcom.3
    cA
    cB
    cC
    hvmulcom
    mp3an
end
