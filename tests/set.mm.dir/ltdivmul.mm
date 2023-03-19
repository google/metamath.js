include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cdiv.mm"
include "wb.mm"
include "remulcl.mm"
include "ancoms.mm"
include "adantrr.mm"
include "3adant1.mm"
include "ltdiv1.mm"
include "syld3an2.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "adantr.mm"
include "ad2antrl.mm"
include "wne.mm"
include "gt0ne0.mm"
include "adantl.mm"
include "divcan3d.mm"
include "breq2d.mm"
include "bitr2d.mm"

theorem ltdivmul
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( ( A / C ) < B <-> A < ( C x. B ) ) )

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
    cC
    cB
    cmul
    co
    #
    clt
    wbr
    #
    cA
    cC
    cdiv
    co
    #
    @6
    cC
    cdiv
    co
    #
    clt
    wbr
    #
    @8
    cB
    clt
    wbr
    @0
    @6
    cr
    wcel
    #
    @1
    @4
    @7
    @10
    wb
    @1
    @4
    @11
    @0
    @1
    @2
    @11
    @3
    @2
    @1
    @11
    cC
    cB
    remulcl
    ancoms
    adantrr
    3adant1
    cA
    @6
    cC
    ltdiv1
    syld3an2
    @5
    @9
    cB
    @8
    clt
    @1
    @4
    @9
    cB
    wceq
    @0
    @1
    @4
    wa
    cB
    cC
    @1
    cB
    cc
    wcel
    @4
    cB
    recn
    adantr
    @2
    cC
    cc
    wcel
    @1
    @3
    cC
    recn
    ad2antrl
    @4
    cC
    cc0
    wne
    @1
    cC
    gt0ne0
    adantl
    divcan3d
    3adant1
    breq2d
    bitr2d
end
