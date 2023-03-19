include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "elfz1end.mm"
include "mpbi.mm"

theorem jm2.27dlem3
  let cA: class A
  assume jm2.27dlem3.1: |- A e. NN


  assert |- A e. ( 1 ... A )

  proof
    cA
    cn
    wcel
    cA
    c1
    cA
    cfz
    co
    wcel
    jm2.27dlem3.1
    cA
    elfz1end
    mpbi
end
