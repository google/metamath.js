include "ccmn.mm"
include "cmnd.mm"
include "bj-cmnssmnd.mm"
include "sseli.mm"

theorem bj-cmnssmndel
  let cA: class A


  assert |- ( A e. CMnd -> A e. Mnd )

  proof
    ccmn
    cmnd
    cA
    bj-cmnssmnd
    sseli
end
