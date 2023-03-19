include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cuz.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "an4.mm"
include "df-3an.mm"
include "anbi1i.mm"
include "eluz2.mm"
include "3ancoma.mm"
include "3bitri.mm"
include "3bitr4i.mm"
include "elfzoelz.mm"
include "elfzoel1.mm"
include "elfzoel2.mm"
include "3jca.mm"
include "elfzo.mm"
include "biadan2.mm"
include "3anass.mm"

theorem elfzo2
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( K e. ( M ..^ N ) <-> ( K e. ( ZZ>= ` M ) /\ N e. ZZ /\ K < N ) )

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
    cM
    cK
    cle
    wbr
    #
    cK
    cN
    clt
    wbr
    #
    wa
    #
    wa
    #
    cK
    cM
    cuz
    cfv
    wcel
    #
    @2
    @5
    wa
    #
    wa
    #
    cK
    cM
    cN
    cfzo
    co
    wcel
    #
    @8
    @2
    @5
    w3a
    @0
    @1
    wa
    #
    @2
    wa
    #
    @6
    wa
    @12
    @4
    wa
    #
    @9
    wa
    @7
    @10
    @12
    @2
    @4
    @5
    an4
    @3
    @13
    @6
    @0
    @1
    @2
    df-3an
    anbi1i
    @8
    @14
    @9
    @8
    @1
    @0
    @4
    w3a
    @0
    @1
    @4
    w3a
    @14
    cM
    cK
    eluz2
    @1
    @0
    @4
    3ancoma
    @0
    @1
    @4
    df-3an
    3bitri
    anbi1i
    3bitr4i
    @11
    @3
    @6
    @11
    @0
    @1
    @2
    cK
    cM
    cN
    elfzoelz
    cK
    cM
    cN
    elfzoel1
    cK
    cM
    cN
    elfzoel2
    3jca
    cK
    cM
    cN
    elfzo
    biadan2
    @8
    @2
    @5
    3anass
    3bitr4i
end
