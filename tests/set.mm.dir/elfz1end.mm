include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "cz.mm"
include "nnz.mm"
include "uzid.mm"
include "syl.mm"
include "eluzfz.mm"
include "syl2anc.mm"
include "elfznn.mm"
include "impbii.mm"

theorem elfz1end
  let cA: class A


  assert |- ( A e. NN <-> A e. ( 1 ... A ) )

  proof
    cA
    cn
    wcel
    #
    cA
    c1
    cA
    cfz
    co
    wcel
    #
    @0
    cA
    c1
    cuz
    cfv
    wcel
    #
    cA
    cA
    cuz
    cfv
    wcel
    #
    @1
    @0
    @2
    cA
    elnnuz
    biimpi
    @0
    cA
    cz
    wcel
    @3
    cA
    nnz
    cA
    uzid
    syl
    cA
    c1
    cA
    eluzfz
    syl2anc
    cA
    cA
    elfznn
    impbii
end
