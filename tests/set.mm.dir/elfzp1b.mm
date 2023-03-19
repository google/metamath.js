include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cmin.mm"
include "cc0.mm"
include "wb.mm"
include "peano2z.mm"
include "1z.mm"
include "fzsubel.mm"
include "mpanl1.mm"
include "mpanr2.mm"
include "sylan2.mm"
include "ancoms.mm"
include "cc.mm"
include "wceq.mm"
include "zcn.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "1m1e0.mm"
include "oveq1i.mm"
include "a1i.mm"
include "eleq12d.mm"
include "adantr.mm"
include "bitr2d.mm"

theorem elfzp1b
  let cK: class K
  let cN: class N


  assert |- ( ( K e. ZZ /\ N e. ZZ ) -> ( K e. ( 0 ... ( N - 1 ) ) <-> ( K + 1 ) e. ( 1 ... N ) ) )

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
    cK
    c1
    caddc
    co
    #
    c1
    cN
    cfz
    co
    wcel
    #
    @2
    c1
    cmin
    co
    #
    c1
    c1
    cmin
    co
    #
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
    cc0
    @6
    cfz
    co
    #
    wcel
    #
    @1
    @0
    @3
    @8
    wb
    #
    @0
    @1
    @2
    cz
    wcel
    #
    @11
    cK
    peano2z
    @1
    @12
    c1
    cz
    wcel
    #
    @11
    1z
    @13
    @1
    @12
    @13
    wa
    @11
    1z
    @2
    c1
    c1
    cN
    fzsubel
    mpanl1
    mpanr2
    sylan2
    ancoms
    @0
    @8
    @10
    wb
    @1
    @0
    @4
    cK
    @7
    @9
    @0
    cK
    cc
    wcel
    c1
    cc
    wcel
    @4
    cK
    wceq
    cK
    zcn
    ax-1cn
    cK
    c1
    pncan
    sylancl
    @7
    @9
    wceq
    @0
    @5
    cc0
    @6
    cfz
    1m1e0
    oveq1i
    a1i
    eleq12d
    adantr
    bitr2d
end
