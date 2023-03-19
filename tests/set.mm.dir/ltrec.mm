include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "wb.mm"
include "1red.mm"
include "simprl.mm"
include "simpll.mm"
include "simplr.mm"
include "ltmuldiv.mm"
include "syl112anc.mm"
include "recnd.mm"
include "mulid2d.mm"
include "breq1d.mm"
include "gt0ne0d.mm"
include "divrecd.mm"
include "breq2d.mm"
include "3bitr3d.mm"
include "rereccld.mm"
include "simprr.mm"
include "ltdivmul.mm"
include "bitr4d.mm"

theorem ltrec
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) ) -> ( A < B <-> ( 1 / B ) < ( 1 / A ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    clt
    wbr
    #
    wa
    #
    cB
    cr
    wcel
    #
    cc0
    cB
    clt
    wbr
    #
    wa
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    c1
    cB
    c1
    cA
    cdiv
    co
    #
    cmul
    co
    #
    clt
    wbr
    #
    c1
    cB
    cdiv
    co
    @8
    clt
    wbr
    #
    @6
    c1
    cA
    cmul
    co
    #
    cB
    clt
    wbr
    #
    c1
    cB
    cA
    cdiv
    co
    #
    clt
    wbr
    #
    @7
    @10
    @6
    c1
    cr
    wcel
    #
    @3
    @0
    @1
    @13
    @15
    wb
    @6
    1red
    #
    @2
    @3
    @4
    simprl
    #
    @0
    @1
    @5
    simpll
    #
    @0
    @1
    @5
    simplr
    #
    c1
    cB
    cA
    ltmuldiv
    syl112anc
    @6
    @12
    cA
    cB
    clt
    @6
    cA
    @6
    cA
    @19
    recnd
    #
    mulid2d
    breq1d
    @6
    @14
    @9
    c1
    clt
    @6
    cB
    cA
    @6
    cB
    @18
    recnd
    @21
    @6
    cA
    @20
    gt0ne0d
    #
    divrecd
    breq2d
    3bitr3d
    @6
    @16
    @8
    cr
    wcel
    @3
    @4
    @11
    @10
    wb
    @17
    @6
    cA
    @19
    @22
    rereccld
    @18
    @2
    @3
    @4
    simprr
    c1
    @8
    cB
    ltdivmul
    syl112anc
    bitr4d
end
