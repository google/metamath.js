include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "cmin.mm"
include "co.mm"
include "cn0.mm"
include "eluz2.mm"
include "znn0sub.mm"
include "biimp3a.mm"
include "sylbi.mm"

theorem uznn0sub
  let cM: class M
  let cN: class N


  assert |- ( N e. ( ZZ>= ` M ) -> ( N - M ) e. NN0 )

  proof
    cN
    cM
    cuz
    cfv
    wcel
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cM
    cN
    cle
    wbr
    #
    w3a
    cN
    cM
    cmin
    co
    cn0
    wcel
    #
    cM
    cN
    eluz2
    @0
    @1
    @2
    @3
    cM
    cN
    znn0sub
    biimp3a
    sylbi
end
