include "cz.mm"
include "wcel.mm"
include "cfz.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wb.mm"
include "w3a.mm"
include "elfz1.mm"
include "3anass.mm"
include "baib.mm"
include "sylan9bb.mm"
include "3impa.mm"
include "3comr.mm"

theorem elfz
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( K e. ( M ... N ) <-> ( M <_ K /\ K <_ N ) ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    cK
    cM
    cN
    cfz
    co
    wcel
    #
    cM
    cK
    cle
    wbr
    #
    cK
    cN
    cle
    wbr
    #
    wa
    #
    wb
    #
    @0
    @1
    @2
    @7
    @0
    @1
    wa
    @3
    @2
    @4
    @5
    w3a
    #
    @2
    @6
    cK
    cM
    cN
    elfz1
    @8
    @2
    @6
    @2
    @4
    @5
    3anass
    baib
    sylan9bb
    3impa
    3comr
end
