include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfzo.mm"
include "clt.mm"
include "wb.mm"
include "peano2zm.mm"
include "elfz.mm"
include "syl3an3.mm"
include "fzoval.mm"
include "eleq2d.mm"
include "3ad2ant3.mm"
include "zltlem1.mm"
include "3adant2.mm"
include "anbi2d.mm"
include "3bitr4d.mm"

theorem elfzo
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( K e. ( M ..^ N ) <-> ( M <_ K /\ K < N ) ) )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cK
    cM
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
    cM
    cK
    cle
    wbr
    #
    cK
    @4
    cle
    wbr
    #
    wa
    #
    cK
    cM
    cN
    cfzo
    co
    #
    wcel
    #
    @7
    cK
    cN
    clt
    wbr
    #
    wa
    @2
    @0
    @1
    @4
    cz
    wcel
    @6
    @9
    wb
    cN
    peano2zm
    cK
    cM
    @4
    elfz
    syl3an3
    @2
    @0
    @11
    @6
    wb
    @1
    @2
    @10
    @5
    cK
    cM
    cN
    fzoval
    eleq2d
    3ad2ant3
    @3
    @12
    @8
    @7
    @0
    @2
    @12
    @8
    wb
    @1
    cK
    cN
    zltlem1
    3adant2
    anbi2d
    3bitr4d
end
