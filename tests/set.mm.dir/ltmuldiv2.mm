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
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "adantrr.mm"
include "3adant2.mm"
include "breq1d.mm"
include "ltmuldiv.mm"
include "bitr3d.mm"

theorem ltmuldiv2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( ( C x. A ) < B <-> A < ( B / C ) ) )

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
    cmul
    co
    #
    cB
    clt
    wbr
    cC
    cA
    cmul
    co
    #
    cB
    clt
    wbr
    cA
    cB
    cC
    cdiv
    co
    clt
    wbr
    @5
    @6
    @7
    cB
    clt
    @0
    @4
    @6
    @7
    wceq
    #
    @1
    @0
    @2
    @8
    @3
    @0
    cA
    cc
    wcel
    cC
    cc
    wcel
    @8
    @2
    cA
    recn
    cC
    recn
    cA
    cC
    mulcom
    syl2an
    adantrr
    3adant2
    breq1d
    cA
    cB
    cC
    ltmuldiv
    bitr3d
end
