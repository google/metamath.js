include "cc.mm"
include "wcel.mm"
include "chil.mm"
include "cmul.mm"
include "co.mm"
include "csm.mm"
include "wceq.mm"
include "ax-hvmulass.mm"
include "mp3an.mm"

theorem hvmulassi
  let cA: class A
  let cB: class B
  let cC: class C
  assume hvmulcom.1: |- A e. CC
  assume hvmulcom.2: |- B e. CC
  assume hvmulcom.3: |- C e. ~H


  assert |- ( ( A x. B ) .h C ) = ( A .h ( B .h C ) )

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
    cmul
    co
    cC
    csm
    co
    cA
    cB
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
    ax-hvmulass
    mp3an
end
