include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "wceq.mm"
include "wo.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "ltmul1.mm"
include "cc.mm"
include "wne.mm"
include "wb.mm"
include "recn.mm"
include "adantr.mm"
include "gt0ne0.mm"
include "jca.mm"
include "mulcan2.mm"
include "syl3an.mm"
include "bicomd.mm"
include "orbi12d.mm"
include "leloe.mm"
include "3adant3.mm"
include "remulcl.mm"
include "3adant2.mm"
include "3adant1.mm"
include "leloed.mm"
include "3adant3r.mm"
include "3bitr4d.mm"

theorem lemul1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( A <_ B <-> ( A x. C ) <_ ( B x. C ) ) )

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
    cA
    cB
    wceq
    #
    wo
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
    #
    @9
    @10
    wceq
    #
    wo
    #
    cA
    cB
    cle
    wbr
    #
    @9
    @10
    cle
    wbr
    #
    @5
    @6
    @11
    @7
    @12
    cA
    cB
    cC
    ltmul1
    @5
    @12
    @7
    @0
    cA
    cc
    wcel
    @1
    cB
    cc
    wcel
    @4
    cC
    cc
    wcel
    #
    cC
    cc0
    wne
    #
    wa
    @12
    @7
    wb
    cA
    recn
    cB
    recn
    @4
    @16
    @17
    @2
    @16
    @3
    cC
    recn
    adantr
    cC
    gt0ne0
    jca
    cA
    cB
    cC
    mulcan2
    syl3an
    bicomd
    orbi12d
    @0
    @1
    @14
    @8
    wb
    @4
    cA
    cB
    leloe
    3adant3
    @0
    @1
    @2
    @15
    @13
    wb
    @3
    @0
    @1
    @2
    w3a
    @9
    @10
    @0
    @2
    @9
    cr
    wcel
    @1
    cA
    cC
    remulcl
    3adant2
    @1
    @2
    @10
    cr
    wcel
    @0
    cB
    cC
    remulcl
    3adant1
    leloed
    3adant3r
    3bitr4d
end
