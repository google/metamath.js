include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "ltrec.mm"
include "ancoms.mm"
include "notbid.mm"
include "simpll.mm"
include "simprl.mm"
include "lenltd.mm"
include "simprr.mm"
include "gt0ne0d.mm"
include "rereccld.mm"
include "simplr.mm"
include "3bitr4d.mm"

theorem lerec
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 < A ) /\ ( B e. RR /\ 0 < B ) ) -> ( A <_ B <-> ( 1 / B ) <_ ( 1 / A ) ) )

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
    cB
    cA
    clt
    wbr
    #
    wn
    c1
    cA
    cdiv
    co
    #
    c1
    cB
    cdiv
    co
    #
    clt
    wbr
    #
    wn
    cA
    cB
    cle
    wbr
    @9
    @8
    cle
    wbr
    @6
    @7
    @10
    @5
    @2
    @7
    @10
    wb
    cB
    cA
    ltrec
    ancoms
    notbid
    @6
    cA
    cB
    @0
    @1
    @5
    simpll
    #
    @2
    @3
    @4
    simprl
    #
    lenltd
    @6
    @9
    @8
    @6
    cB
    @12
    @6
    cB
    @2
    @3
    @4
    simprr
    gt0ne0d
    rereccld
    @6
    cA
    @11
    @6
    cA
    @0
    @1
    @5
    simplr
    gt0ne0d
    rereccld
    lenltd
    3bitr4d
end
