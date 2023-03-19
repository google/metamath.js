include "wne.mm"
include "csn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cxp.mm"
include "disjsn2.mm"
include "xpdisj2.mm"
include "syl.mm"

theorem xpsndisj
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( B =/= D -> ( ( A X. { B } ) i^i ( C X. { D } ) ) = (/) )

  proof
    cB
    cD
    wne
    cB
    csn
    #
    cD
    csn
    #
    cin
    c0
    wceq
    cA
    @0
    cxp
    cC
    @1
    cxp
    cin
    c0
    wceq
    cB
    cD
    disjsn2
    @0
    @1
    cA
    cC
    xpdisj2
    syl
end
