include "con0.mm"
include "wcel.mm"
include "w3a.mm"
include "c0.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "comu.mm"
include "co.mm"
include "wss.mm"
include "omord2.mm"
include "wb.mm"
include "3anrot.mm"
include "omcan.mm"
include "sylanbr.mm"
include "bicomd.mm"
include "orbi12d.mm"
include "onsseleq.mm"
include "3adant3.mm"
include "adantr.mm"
include "omcl.mm"
include "anim12dan.mm"
include "ancoms.mm"
include "3impa.mm"
include "syl.mm"
include "3bitr4d.mm"

theorem omword
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. On /\ B e. On /\ C e. On ) /\ (/) e. C ) -> ( A C_ B <-> ( C .o A ) C_ ( C .o B ) ) )

  proof
    cA
    con0
    wcel
    #
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    w3a
    #
    c0
    cC
    wcel
    #
    wa
    #
    cA
    cB
    wcel
    #
    cA
    cB
    wceq
    #
    wo
    #
    cC
    cA
    comu
    co
    #
    cC
    cB
    comu
    co
    #
    wcel
    #
    @9
    @10
    wceq
    #
    wo
    #
    cA
    cB
    wss
    #
    @9
    @10
    wss
    #
    @5
    @6
    @11
    @7
    @12
    cA
    cB
    cC
    omord2
    @5
    @12
    @7
    @3
    @2
    @0
    @1
    w3a
    @4
    @12
    @7
    wb
    @2
    @0
    @1
    3anrot
    cC
    cA
    cB
    omcan
    sylanbr
    bicomd
    orbi12d
    @3
    @14
    @8
    wb
    #
    @4
    @0
    @1
    @16
    @2
    cA
    cB
    onsseleq
    3adant3
    adantr
    @3
    @15
    @13
    wb
    #
    @4
    @3
    @9
    con0
    wcel
    #
    @10
    con0
    wcel
    #
    wa
    #
    @17
    @0
    @1
    @2
    @20
    @2
    @0
    @1
    wa
    @20
    @2
    @0
    @18
    @1
    @19
    cC
    cA
    omcl
    cC
    cB
    omcl
    anim12dan
    ancoms
    3impa
    @9
    @10
    onsseleq
    syl
    adantr
    3bitr4d
end
