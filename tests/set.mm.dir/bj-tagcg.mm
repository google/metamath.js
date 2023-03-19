include "wcel.mm"
include "csn.mm"
include "bj-csngl.mm"
include "bj-ctag.mm"
include "bj-snglc.mm"
include "bj-sngltag.mm"
include "syl5bb.mm"

theorem bj-tagcg
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( A e. V -> ( A e. B <-> { A } e. tag B ) )

  proof
    cA
    cB
    wcel
    cA
    csn
    #
    cB
    bj-csngl
    wcel
    cA
    cV
    wcel
    @0
    cB
    bj-ctag
    wcel
    cA
    cB
    bj-snglc
    cA
    cB
    cV
    bj-sngltag
    syl5bb
end
