include "cfzo.mm"
include "co.mm"
include "wnel.mm"
include "wcel.mm"
include "wn.mm"
include "cz.mm"
include "w3a.mm"
include "clt.mm"
include "wbr.mm"
include "cle.mm"
include "wo.mm"
include "df-nel.mm"
include "wa.mm"
include "wb.mm"
include "ianor.mm"
include "a1i.mm"
include "elfzo.mm"
include "notbid.mm"
include "cr.mm"
include "zre.mm"
include "anim12i.mm"
include "3adant3.mm"
include "ltnle.mm"
include "syl.mm"
include "anim12ci.mm"
include "3adant2.mm"
include "lenlt.mm"
include "orbi12d.mm"
include "3bitr4d.mm"
include "syl5bb.mm"

theorem nelfzo
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( K e/ ( M ..^ N ) <-> ( K < M \/ N <_ K ) ) )

  proof
    cK
    cM
    cN
    cfzo
    co
    #
    wnel
    cK
    @0
    wcel
    #
    wn
    #
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
    clt
    wbr
    #
    cN
    cK
    cle
    wbr
    #
    wo
    #
    cK
    @0
    df-nel
    @6
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
    wn
    #
    @10
    wn
    #
    @11
    wn
    #
    wo
    #
    @2
    @9
    @13
    @16
    wb
    @6
    @10
    @11
    ianor
    a1i
    @6
    @1
    @12
    cK
    cM
    cN
    elfzo
    notbid
    @6
    @7
    @14
    @8
    @15
    @6
    cK
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    wa
    #
    @7
    @14
    wb
    @3
    @4
    @19
    @5
    @3
    @17
    @4
    @18
    cK
    zre
    #
    cM
    zre
    anim12i
    3adant3
    cK
    cM
    ltnle
    syl
    @6
    cN
    cr
    wcel
    #
    @17
    wa
    #
    @8
    @15
    wb
    @3
    @5
    @22
    @4
    @3
    @17
    @5
    @21
    @20
    cN
    zre
    anim12ci
    3adant2
    cN
    cK
    lenlt
    syl
    orbi12d
    3bitr4d
    syl5bb
end
