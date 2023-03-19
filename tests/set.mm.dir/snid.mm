include "cvv.mm"
include "wcel.mm"
include "csn.mm"
include "snidb.mm"
include "mpbi.mm"

theorem snid
  let cA: class A
  assume snid.1: |- A e. _V


  assert |- A e. { A }

  proof
    cA
    cvv
    wcel
    cA
    cA
    csn
    wcel
    snid.1
    cA
    snidb
    mpbi
end
