include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "eluzelz.mm"
include "eluzel2.mm"
include "jca.mm"
include "elfz.mm"
include "3expa.mm"
include "sylan.mm"
include "eluzle.mm"
include "biantrurd.mm"
include "adantr.mm"
include "bitr4d.mm"

theorem elfz5
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ( ZZ>= ` M ) /\ N e. ZZ ) -> ( K e. ( M ... N ) <-> K <_ N ) )

  proof
    cK
    cM
    cuz
    cfv
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
    @4
    @0
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    wa
    @1
    @2
    @5
    wb
    #
    @0
    @6
    @7
    cM
    cK
    eluzelz
    cM
    cK
    eluzel2
    jca
    @6
    @7
    @1
    @8
    cK
    cM
    cN
    elfz
    3expa
    sylan
    @0
    @4
    @5
    wb
    @1
    @0
    @3
    @4
    cM
    cK
    eluzle
    biantrurd
    adantr
    bitr4d
end
