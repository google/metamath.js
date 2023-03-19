include "cc.mm"
include "wcel.mm"
include "cre.mm"
include "cfv.mm"
include "cpi.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cneg.mm"
include "cioo.mm"
include "w3a.mm"
include "casin.mm"
include "wceq.mm"
include "csin.mm"
include "sinasin.mm"
include "3ad2ant1.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "syl5ibcom.mm"
include "asinsin.mm"
include "3adant1.mm"
include "impbid.mm"

theorem asinsinb
  let cA: class A
  let cB: class B


  assert |- ( ( A e. CC /\ B e. CC /\ ( Re ` B ) e. ( -u ( _pi / 2 ) (,) ( _pi / 2 ) ) ) -> ( ( arcsin ` A ) = B <-> ( sin ` B ) = A ) )

  proof
    cA
    cc
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
    casin
    cfv
    #
    cB
    wceq
    #
    cB
    csin
    cfv
    #
    cA
    wceq
    #
    @4
    @5
    csin
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
    sinasin
    3ad2ant1
    @6
    @9
    @7
    cA
    @5
    cB
    csin
    fveq2
    eqeq1d
    syl5ibcom
    @4
    @7
    casin
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
    asinsin
    3adant1
    @8
    @11
    @5
    cB
    @7
    cA
    casin
    fveq2
    eqeq1d
    syl5ibcom
    impbid
end
