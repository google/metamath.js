include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "cmul.mm"
include "co.mm"
include "clt.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "0red.mm"
include "simpl.mm"
include "leloed.mm"
include "c1.mm"
include "cdiv.mm"
include "simpll.mm"
include "simplr.mm"
include "remulcld.mm"
include "simprl.mm"
include "gt0ne0d.mm"
include "rereccld.mm"
include "simprr.mm"
include "recgt0.mm"
include "ad2ant2r.mm"
include "mulgt0d.mm"
include "recnd.mm"
include "divrecd.mm"
include "cc.mm"
include "simpr.mm"
include "adantr.mm"
include "divcan3d.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "exp32.mm"
include "0re.mm"
include "ltnri.mm"
include "mul02d.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "pm2.21d.mm"
include "oveq1.mm"
include "imbi1d.mm"
include "syl5ibcom.mm"
include "jaod.mm"
include "sylbid.mm"
include "imp32.mm"

theorem prodgt0
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 0 <_ A /\ 0 < ( A x. B ) ) ) -> 0 < B )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    wa
    #
    cc0
    cA
    cle
    wbr
    #
    cc0
    cA
    cB
    cmul
    co
    #
    clt
    wbr
    #
    cc0
    cB
    clt
    wbr
    #
    @2
    @3
    cc0
    cA
    clt
    wbr
    #
    cc0
    cA
    wceq
    #
    wo
    @5
    @6
    wi
    #
    @2
    cc0
    cA
    @2
    0red
    @0
    @1
    simpl
    leloed
    @2
    @7
    @9
    @8
    @2
    @7
    @5
    @6
    @2
    @7
    @5
    wa
    #
    wa
    #
    cc0
    @4
    c1
    cA
    cdiv
    co
    #
    cmul
    co
    #
    cB
    clt
    @11
    @4
    @12
    @11
    cA
    cB
    @0
    @1
    @10
    simpll
    #
    @0
    @1
    @10
    simplr
    remulcld
    #
    @11
    cA
    @14
    @11
    cA
    @2
    @7
    @5
    simprl
    gt0ne0d
    #
    rereccld
    @2
    @7
    @5
    simprr
    @0
    @7
    cc0
    @12
    clt
    wbr
    @1
    @5
    cA
    recgt0
    ad2ant2r
    mulgt0d
    @11
    @4
    cA
    cdiv
    co
    @13
    cB
    @11
    @4
    cA
    @11
    @4
    @15
    recnd
    @11
    cA
    @14
    recnd
    #
    @16
    divrecd
    @11
    cB
    cA
    @2
    cB
    cc
    wcel
    @10
    @2
    cB
    @0
    @1
    simpr
    recnd
    #
    adantr
    @17
    @16
    divcan3d
    eqtr3d
    breqtrd
    exp32
    @2
    cc0
    cc0
    cB
    cmul
    co
    #
    clt
    wbr
    #
    @6
    wi
    @8
    @9
    @2
    @20
    @6
    @2
    @20
    cc0
    cc0
    clt
    wbr
    cc0
    0re
    ltnri
    @2
    @19
    cc0
    cc0
    clt
    @2
    cB
    @18
    mul02d
    breq2d
    mtbiri
    pm2.21d
    @8
    @20
    @5
    @6
    @8
    @19
    @4
    cc0
    clt
    cc0
    cA
    cB
    cmul
    oveq1
    breq2d
    imbi1d
    syl5ibcom
    jaod
    sylbid
    imp32
end
