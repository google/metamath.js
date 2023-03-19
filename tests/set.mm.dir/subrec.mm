include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "1cnd.mm"
include "simpll.mm"
include "simprl.mm"
include "simplr.mm"
include "simprr.mm"
include "divsubdivd.mm"
include "mulid2d.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "eqtrd.mm"

theorem subrec
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( ( 1 / A ) - ( 1 / B ) ) = ( ( B - A ) / ( A x. B ) ) )

  proof
    cA
    cc
    wcel
    #
    cA
    cc0
    wne
    #
    wa
    #
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    #
    wa
    #
    c1
    cA
    cdiv
    co
    c1
    cB
    cdiv
    co
    cmin
    co
    c1
    cB
    cmul
    co
    #
    c1
    cA
    cmul
    co
    #
    cmin
    co
    #
    cA
    cB
    cmul
    co
    #
    cdiv
    co
    cB
    cA
    cmin
    co
    #
    @10
    cdiv
    co
    @6
    c1
    cA
    c1
    cB
    @6
    1cnd
    #
    @0
    @1
    @5
    simpll
    #
    @12
    @2
    @3
    @4
    simprl
    #
    @0
    @1
    @5
    simplr
    @2
    @3
    @4
    simprr
    divsubdivd
    @6
    @9
    @11
    @10
    cdiv
    @6
    @7
    cB
    @8
    cA
    cmin
    @6
    cB
    @14
    mulid2d
    @6
    cA
    @13
    mulid2d
    oveq12d
    oveq1d
    eqtrd
end
