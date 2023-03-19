include "cn0.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "co.mm"
include "nn0sub.mm"
include "biimp3a.mm"

theorem nn0sub2
  let cM: class M
  let cN: class N


  assert |- ( ( M e. NN0 /\ N e. NN0 /\ M <_ N ) -> ( N - M ) e. NN0 )

  proof
    cM
    cn0
    wcel
    cN
    cn0
    wcel
    cM
    cN
    cle
    wbr
    cN
    cM
    cmin
    co
    cn0
    wcel
    cM
    cN
    nn0sub
    biimp3a
end
