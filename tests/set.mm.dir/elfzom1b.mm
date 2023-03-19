include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cc0.mm"
include "cfzo.mm"
include "wb.mm"
include "peano2zm.mm"
include "elfzm1b.mm"
include "sylan2.mm"
include "wceq.mm"
include "fzoval.mm"
include "adantl.mm"
include "eleq2d.mm"
include "syl.mm"
include "3bitr4d.mm"

theorem elfzom1b
  let cK: class K
  let cN: class N


  assert |- ( ( K e. ZZ /\ N e. ZZ ) -> ( K e. ( 1 ..^ N ) <-> ( K - 1 ) e. ( 0 ..^ ( N - 1 ) ) ) )

  proof
    cK
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cK
    c1
    cN
    c1
    cmin
    co
    #
    cfz
    co
    #
    wcel
    #
    cK
    c1
    cmin
    co
    #
    cc0
    @3
    c1
    cmin
    co
    cfz
    co
    #
    wcel
    #
    cK
    c1
    cN
    cfzo
    co
    #
    wcel
    @6
    cc0
    @3
    cfzo
    co
    #
    wcel
    @1
    @0
    @3
    cz
    wcel
    #
    @5
    @8
    wb
    cN
    peano2zm
    #
    cK
    @3
    elfzm1b
    sylan2
    @2
    @9
    @4
    cK
    @1
    @9
    @4
    wceq
    @0
    c1
    cN
    fzoval
    adantl
    eleq2d
    @2
    @10
    @7
    @6
    @2
    @11
    @10
    @7
    wceq
    @1
    @11
    @0
    @12
    adantl
    cc0
    @3
    fzoval
    syl
    eleq2d
    3bitr4d
end
