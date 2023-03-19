include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cfz.mm"
include "co.mm"
include "cuz.mm"
include "cfv.mm"
include "df-3an.mm"
include "an6.mm"
include "anandir.mm"
include "ancom.mm"
include "anbi2i.mm"
include "3bitri.mm"
include "anbi1i.mm"
include "3bitr4ri.mm"
include "elfz2.mm"
include "eluz2.mm"
include "anbi12i.mm"
include "3bitr4i.mm"

theorem elfzuzb
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ... N ) <-> ( K e. ( ZZ>= ` M ) /\ N e. ( ZZ>= ` K ) ) )

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
    w3a
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
    wa
    #
    @0
    @2
    @4
    w3a
    #
    @2
    @1
    @5
    w3a
    #
    wa
    #
    cK
    cM
    cN
    cfz
    co
    wcel
    cK
    cM
    cuz
    cfv
    wcel
    #
    cN
    cK
    cuz
    cfv
    wcel
    #
    wa
    @0
    @2
    wa
    #
    @2
    @1
    wa
    #
    @6
    w3a
    @13
    @14
    wa
    #
    @6
    wa
    @10
    @7
    @13
    @14
    @6
    df-3an
    @0
    @2
    @4
    @2
    @1
    @5
    an6
    @3
    @15
    @6
    @3
    @0
    @1
    wa
    @2
    wa
    @13
    @1
    @2
    wa
    #
    wa
    @15
    @0
    @1
    @2
    df-3an
    @0
    @1
    @2
    anandir
    @16
    @14
    @13
    @1
    @2
    ancom
    anbi2i
    3bitri
    anbi1i
    3bitr4ri
    cK
    cM
    cN
    elfz2
    @11
    @8
    @12
    @9
    cM
    cK
    eluz2
    cK
    cN
    eluz2
    anbi12i
    3bitr4i
end
