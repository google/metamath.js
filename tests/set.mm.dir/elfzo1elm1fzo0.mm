include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cfzo.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "elfzoelz.mm"
include "elfzoel2.mm"
include "jca.mm"
include "elfzom1b.mm"
include "biimpd.mm"
include "mpcom.mm"

theorem elfzo1elm1fzo0
  let cI: class I
  let cN: class N


  assert |- ( I e. ( 1 ..^ N ) -> ( I - 1 ) e. ( 0 ..^ ( N - 1 ) ) )

  proof
    cI
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cI
    c1
    cN
    cfzo
    co
    wcel
    #
    cI
    c1
    cmin
    co
    cc0
    cN
    c1
    cmin
    co
    cfzo
    co
    wcel
    #
    @3
    @0
    @1
    cI
    c1
    cN
    elfzoelz
    cI
    c1
    cN
    elfzoel2
    jca
    @2
    @3
    @4
    cI
    cN
    elfzom1b
    biimpd
    mpcom
end
