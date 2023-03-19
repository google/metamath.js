include "cz.mm"
include "wcel.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cmin.mm"
include "cc0.mm"
include "wb.mm"
include "wa.mm"
include "1z.mm"
include "fzsubel.mm"
include "mpanl1.mm"
include "mpanr2.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "eleq2i.mm"
include "syl6bb.mm"
include "ancoms.mm"

theorem elfzm1b
  let cK: class K
  let cN: class N


  assert |- ( ( K e. ZZ /\ N e. ZZ ) -> ( K e. ( 1 ... N ) <-> ( K - 1 ) e. ( 0 ... ( N - 1 ) ) ) )

  proof
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    cK
    c1
    cN
    cfz
    co
    wcel
    #
    cK
    c1
    cmin
    co
    #
    cc0
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
    wb
    @0
    @1
    wa
    @2
    @3
    c1
    c1
    cmin
    co
    #
    @4
    cfz
    co
    #
    wcel
    #
    @6
    @0
    @1
    c1
    cz
    wcel
    #
    @2
    @9
    wb
    #
    1z
    @10
    @0
    @1
    @10
    wa
    @11
    1z
    cK
    c1
    c1
    cN
    fzsubel
    mpanl1
    mpanr2
    @8
    @5
    @3
    @7
    cc0
    @4
    cfz
    1m1e0
    oveq1i
    eleq2i
    syl6bb
    ancoms
end
