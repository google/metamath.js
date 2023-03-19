include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cmin.mm"
include "simpl2.mm"
include "simpl1.mm"
include "resubcld.mm"
include "simpl3l.mm"
include "simpr.mm"
include "posdifd.mm"
include "mpbid.mm"
include "simpl3r.mm"
include "mulgt0d.mm"
include "recnd.mm"
include "subdird.mm"
include "breqtrd.mm"
include "remulcld.mm"
include "mpbird.mm"

theorem ltmul1a
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) /\ A < B ) -> ( A x. C ) < ( B x. C ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    clt
    wbr
    #
    wa
    #
    w3a
    #
    cA
    cB
    clt
    wbr
    #
    wa
    #
    cA
    cC
    cmul
    co
    #
    cB
    cC
    cmul
    co
    #
    clt
    wbr
    cc0
    @9
    @8
    cmin
    co
    #
    clt
    wbr
    @7
    cc0
    cB
    cA
    cmin
    co
    #
    cC
    cmul
    co
    @10
    clt
    @7
    @11
    cC
    @7
    cB
    cA
    @0
    @1
    @4
    @6
    simpl2
    #
    @0
    @1
    @4
    @6
    simpl1
    #
    resubcld
    @2
    @3
    @0
    @1
    @6
    simpl3l
    #
    @7
    @6
    cc0
    @11
    clt
    wbr
    @5
    @6
    simpr
    @7
    cA
    cB
    @13
    @12
    posdifd
    mpbid
    @2
    @3
    @0
    @1
    @6
    simpl3r
    mulgt0d
    @7
    cB
    cA
    cC
    @7
    cB
    @12
    recnd
    @7
    cA
    @13
    recnd
    @7
    cC
    @14
    recnd
    subdird
    breqtrd
    @7
    @8
    @9
    @7
    cA
    cC
    @13
    @14
    remulcld
    @7
    cB
    cC
    @12
    @14
    remulcld
    posdifd
    mpbird
end
