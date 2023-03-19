include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "cdvds.mm"
include "wbr.mm"
include "cabs.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cz.mm"
include "wb.mm"
include "elfzoel2.mm"
include "elfzoel1.mm"
include "zsubcld.mm"
include "adantl.mm"
include "elfzoelz.mm"
include "zsubcl.mm"
include "syl2an.mm"
include "dvdsabsb.mm"
include "syl2anc.mm"
include "fzomaxdif.mm"
include "fzo0dvdseq.mm"
include "syl.mm"
include "bitrd.mm"
include "cc.mm"
include "zcnd.mm"
include "subcl.mm"
include "abs00ad.mm"
include "subeq0.mm"

theorem fzocongeq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. ( C ..^ D ) /\ B e. ( C ..^ D ) ) -> ( ( D - C ) || ( A - B ) <-> A = B ) )

  proof
    cA
    cC
    cD
    cfzo
    co
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cD
    cC
    cmin
    co
    #
    cA
    cB
    cmin
    co
    #
    cdvds
    wbr
    #
    @5
    cabs
    cfv
    #
    cc0
    wceq
    #
    cA
    cB
    wceq
    #
    @3
    @6
    @4
    @7
    cdvds
    wbr
    #
    @8
    @3
    @4
    cz
    wcel
    #
    @5
    cz
    wcel
    #
    @6
    @10
    wb
    @2
    @11
    @1
    @2
    cD
    cC
    cB
    cC
    cD
    elfzoel2
    cB
    cC
    cD
    elfzoel1
    zsubcld
    adantl
    @1
    cA
    cz
    wcel
    cB
    cz
    wcel
    @12
    @2
    cA
    cC
    cD
    elfzoelz
    #
    cB
    cC
    cD
    elfzoelz
    #
    cA
    cB
    zsubcl
    syl2an
    @4
    @5
    dvdsabsb
    syl2anc
    @3
    @7
    cc0
    @4
    cfzo
    co
    wcel
    @10
    @8
    wb
    cA
    cB
    cC
    cD
    fzomaxdif
    @4
    @7
    fzo0dvdseq
    syl
    bitrd
    @3
    @8
    @5
    cc0
    wceq
    #
    @9
    @3
    @5
    @1
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @5
    cc
    wcel
    @2
    @1
    cA
    @13
    zcnd
    #
    @2
    cB
    @14
    zcnd
    #
    cA
    cB
    subcl
    syl2an
    abs00ad
    @1
    @16
    @17
    @15
    @9
    wb
    @2
    @18
    @19
    cA
    cB
    subeq0
    syl2an
    bitrd
    bitrd
end
