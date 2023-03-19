include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "cgcdOLD.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "cv.mm"
include "cdiv.mm"
include "crab.mm"
include "csup.mm"
include "wb.mm"
include "wi.mm"
include "w3a.mm"
include "nndivsub.mm"
include "exp32.mm"
include "com23.mm"
include "3expia.mm"
include "imp.mm"
include "pm5.32d.mm"
include "rabbidva.mm"
include "supeq1d.mm"
include "df-gcdOLD.mm"
include "3eqtr4g.mm"
include "ex.mm"

theorem ee7.2aOLD
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A e. NN /\ B e. NN ) -> ( A < B -> gcdOLD ( A , B ) = gcdOLD ( A , ( B - A ) ) ) )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    #
    cA
    cB
    clt
    wbr
    #
    cA
    cB
    cgcdOLD
    #
    cA
    cB
    cA
    cmin
    co
    #
    cgcdOLD
    #
    wceq
    @2
    @3
    wa
    #
    cA
    vx
    cv
    #
    cdiv
    co
    cn
    wcel
    #
    cB
    @8
    cdiv
    co
    cn
    wcel
    #
    wa
    #
    vx
    cn
    crab
    #
    cn
    clt
    csup
    @9
    @5
    @8
    cdiv
    co
    cn
    wcel
    #
    wa
    #
    vx
    cn
    crab
    #
    cn
    clt
    csup
    @4
    @6
    @7
    cn
    @12
    @15
    clt
    @7
    @11
    @14
    vx
    cn
    @7
    @8
    cn
    wcel
    #
    wa
    @9
    @10
    @13
    @7
    @16
    @9
    @10
    @13
    wb
    #
    wi
    #
    @2
    @3
    @16
    @18
    wi
    @2
    @16
    @3
    @18
    @0
    @1
    @16
    @3
    @18
    wi
    @0
    @1
    @16
    w3a
    #
    @9
    @3
    @17
    @19
    @9
    @3
    @17
    cA
    cB
    @8
    nndivsub
    exp32
    com23
    3expia
    com23
    imp
    imp
    pm5.32d
    rabbidva
    supeq1d
    vx
    cA
    cB
    df-gcdOLD
    vx
    cA
    @5
    df-gcdOLD
    3eqtr4g
    ex
end
