include "cabl.mm"
include "ccmn.mm"
include "bj-ablsscmn.mm"
include "sseli.mm"

theorem bj-ablsscmnel
  let cA: class A


  assert |- ( A e. Abel -> A e. CMnd )

  proof
    cabl
    ccmn
    cA
    bj-ablsscmn
    sseli
end
