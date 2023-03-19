include "con0.mm"
include "wcel.mm"
include "c2o.mm"
include "cdif.mm"
include "w3a.mm"
include "wceq.mm"
include "wo.mm"
include "coe.mm"
include "co.mm"
include "wss.mm"
include "oeord.mm"
include "wb.mm"
include "oecan.mm"
include "3coml.mm"
include "bicomd.mm"
include "orbi12d.mm"
include "onsseleq.mm"
include "3adant3.mm"
include "wa.mm"
include "eldifi.mm"
include "id.mm"
include "oecl.mm"
include "anim12dan.mm"
include "syl.mm"
include "syl2anr.mm"
include "3impa.mm"
include "3bitr4d.mm"

theorem oeword
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. On /\ B e. On /\ C e. ( On \ 2o ) ) -> ( A C_ B <-> ( C ^o A ) C_ ( C ^o B ) ) )

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
    c2o
    cdif
    wcel
    #
    w3a
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
    coe
    co
    #
    cC
    cB
    coe
    co
    #
    wcel
    #
    @7
    @8
    wceq
    #
    wo
    #
    cA
    cB
    wss
    #
    @7
    @8
    wss
    #
    @3
    @4
    @9
    @5
    @10
    cA
    cB
    cC
    oeord
    @3
    @10
    @5
    @2
    @0
    @1
    @10
    @5
    wb
    cC
    cA
    cB
    oecan
    3coml
    bicomd
    orbi12d
    @0
    @1
    @12
    @6
    wb
    @2
    cA
    cB
    onsseleq
    3adant3
    @0
    @1
    @2
    @13
    @11
    wb
    #
    @2
    cC
    con0
    wcel
    #
    @0
    @1
    wa
    #
    @14
    @16
    cC
    con0
    c2o
    eldifi
    @16
    id
    @15
    @16
    wa
    @7
    con0
    wcel
    #
    @8
    con0
    wcel
    #
    wa
    @14
    @15
    @0
    @17
    @1
    @18
    cC
    cA
    oecl
    cC
    cB
    oecl
    anim12dan
    @7
    @8
    onsseleq
    syl
    syl2anr
    3impa
    3bitr4d
end
