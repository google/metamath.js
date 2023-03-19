include "cssr.mm"
include "cres.mm"
include "ccnv.mm"
include "wbr.mm"
include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "relres.mm"
include "relbrcnv.mm"
include "brssrres.mm"
include "syl5bb.mm"

theorem br1cnvssrres
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V


  assert |- ( B e. V -> ( B `' ( _S |` A ) C <-> ( C e. A /\ C C_ B ) ) )

  proof
    cB
    cC
    cssr
    cA
    cres
    #
    ccnv
    wbr
    cC
    cB
    @0
    wbr
    cB
    cV
    wcel
    cC
    cA
    wcel
    cC
    cB
    wss
    wa
    cB
    cC
    @0
    cssr
    cA
    relres
    relbrcnv
    cA
    cC
    cB
    cV
    brssrres
    syl5bb
end
