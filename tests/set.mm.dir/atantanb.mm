include "catan.mm"
include "cdm.mm"
include "wcel.mm"
include "cc.mm"
include "cre.mm"
include "cfv.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cioo.mm"
include "w3a.mm"
include "wceq.mm"
include "ctan.mm"
include "tanatan.mm"
include "3ad2ant1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "atantan.mm"
include "3adant1.mm"
include "impbid.mm"

theorem atantanb
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom arctan /\ B e. CC /\ ( Re ` B ) e. ( -u ( _pi / 2 ) (,) ( _pi / 2 ) ) ) -> ( ( arctan ` A ) = B <-> ( tan ` B ) = A ) )

  proof
    cA
    catan
    cdm
    wcel
    #
    cB
    cc
    wcel
    #
    cB
    cre
    cfv
    cpi
    c2
    cdiv
    co
    #
    cneg
    @2
    cioo
    co
    wcel
    #
    w3a
    #
    cA
    catan
    cfv
    #
    cB
    wceq
    #
    cB
    ctan
    cfv
    #
    cA
    wceq
    #
    @4
    @5
    ctan
    cfv
    #
    cA
    wceq
    #
    @6
    @8
    @0
    @1
    @10
    @3
    cA
    tanatan
    3ad2ant1
    @6
    @9
    @7
    cA
    @5
    cB
    ctan
    fveq2
    eqeq1d
    syl5ibcom
    @4
    @7
    catan
    cfv
    #
    cB
    wceq
    #
    @8
    @6
    @1
    @3
    @12
    @0
    cB
    atantan
    3adant1
    @8
    @11
    @5
    cB
    @7
    cA
    catan
    fveq2
    eqeq1d
    syl5ibcom
    impbid
end
