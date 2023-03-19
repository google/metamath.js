include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cneg.mm"
include "simprr.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antrl.mm"
include "ad2antlr.mm"
include "negsubdi2d.mm"
include "breqtrrd.mm"
include "wb.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "zsubcld.mm"
include "dvdsnegb.mm"
include "syl2anc.mm"
include "mpbird.mm"

theorem congsym
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. ZZ /\ B e. ZZ ) /\ ( C e. ZZ /\ A || ( B - C ) ) ) -> A || ( C - B ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    cC
    cz
    wcel
    #
    cA
    cB
    cC
    cmin
    co
    #
    cdvds
    wbr
    #
    wa
    #
    wa
    #
    cA
    cC
    cB
    cmin
    co
    #
    cdvds
    wbr
    #
    cA
    @8
    cneg
    #
    cdvds
    wbr
    #
    @7
    cA
    @4
    @10
    cdvds
    @2
    @3
    @5
    simprr
    @7
    cC
    cB
    @3
    cC
    cc
    wcel
    @2
    @5
    cC
    zcn
    ad2antrl
    @1
    cB
    cc
    wcel
    @0
    @6
    cB
    zcn
    ad2antlr
    negsubdi2d
    breqtrrd
    @7
    @0
    @8
    cz
    wcel
    @9
    @11
    wb
    @0
    @1
    @6
    simpll
    @7
    cC
    cB
    @2
    @3
    @5
    simprl
    @0
    @1
    @6
    simplr
    zsubcld
    cA
    @8
    dvdsnegb
    syl2anc
    mpbird
end
