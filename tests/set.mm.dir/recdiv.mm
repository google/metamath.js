include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wa.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cmul.mm"
include "1div1e1.mm"
include "oveq1i.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "ax-1ne0.mm"
include "pm3.2i.mm"
include "divdivdiv.mm"
include "mpanl12.mm"
include "syl5eqr.mm"
include "mulid2.mm"
include "oveqan12rd.mm"
include "ad2ant2r.mm"
include "eqtrd.mm"

theorem recdiv
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. CC /\ A =/= 0 ) /\ ( B e. CC /\ B =/= 0 ) ) -> ( 1 / ( A / B ) ) = ( B / A ) )

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
    cB
    cc
    wcel
    #
    cB
    cc0
    wne
    #
    wa
    wa
    #
    c1
    cA
    cB
    cdiv
    co
    #
    cdiv
    co
    #
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
    cdiv
    co
    #
    cB
    cA
    cdiv
    co
    #
    @4
    @6
    c1
    c1
    cdiv
    co
    #
    @5
    cdiv
    co
    #
    @9
    @11
    c1
    @5
    cdiv
    1div1e1
    oveq1i
    c1
    cc
    wcel
    #
    @13
    c1
    cc0
    wne
    #
    wa
    @4
    @12
    @9
    wceq
    ax-1cn
    @13
    @14
    ax-1cn
    ax-1ne0
    pm3.2i
    c1
    c1
    cA
    cB
    divdivdiv
    mpanl12
    syl5eqr
    @0
    @2
    @9
    @10
    wceq
    @1
    @3
    @2
    @0
    @7
    cB
    @8
    cA
    cdiv
    cB
    mulid2
    cA
    mulid2
    oveqan12rd
    ad2ant2r
    eqtrd
end
