include "cprime.mm"
include "wcel.mm"
include "c2.mm"
include "cuz.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cn0.mm"
include "prmuz2.mm"
include "uznn0sub.mm"
include "syl.mm"

theorem prmm2nn0
  let cP: class P


  assert |- ( P e. Prime -> ( P - 2 ) e. NN0 )

  proof
    cP
    cprime
    wcel
    cP
    c2
    cuz
    cfv
    wcel
    cP
    c2
    cmin
    co
    cn0
    wcel
    cP
    prmuz2
    c2
    cP
    uznn0sub
    syl
end
