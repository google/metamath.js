include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cle.mm"
include "wbr.mm"
include "w3a.mm"
include "clt.mm"
include "wb.mm"
include "peano2zm.mm"
include "elfz1.mm"
include "sylan2.mm"
include "zltlem1.mm"
include "anbi2d.mm"
include "expcom.mm"
include "pm5.32d.mm"
include "3anass.mm"
include "3bitr4g.mm"
include "adantl.mm"
include "bitr4d.mm"

theorem elfzm11
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( K e. ( M ... ( N - 1 ) ) <-> ( K e. ZZ /\ M <_ K /\ K < N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    cK
    cM
    cN
    c1
    cmin
    co
    #
    cfz
    co
    wcel
    #
    cK
    cz
    wcel
    #
    cM
    cK
    cle
    wbr
    #
    cK
    @2
    cle
    wbr
    #
    w3a
    #
    @4
    @5
    cK
    cN
    clt
    wbr
    #
    w3a
    #
    @1
    @0
    @2
    cz
    wcel
    @3
    @7
    wb
    cN
    peano2zm
    cK
    cM
    @2
    elfz1
    sylan2
    @1
    @9
    @7
    wb
    @0
    @1
    @4
    @5
    @8
    wa
    #
    wa
    @4
    @5
    @6
    wa
    #
    wa
    @9
    @7
    @1
    @4
    @10
    @11
    @4
    @1
    @10
    @11
    wb
    @4
    @1
    wa
    @8
    @6
    @5
    cK
    cN
    zltlem1
    anbi2d
    expcom
    pm5.32d
    @4
    @5
    @8
    3anass
    @4
    @5
    @6
    3anass
    3bitr4g
    adantl
    bitr4d
end
