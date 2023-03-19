include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "cdiv.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "adantrr.mm"
include "3adant2.mm"
include "breq1d.mm"
include "lemuldiv.mm"
include "bitr3d.mm"

theorem lemuldiv2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( ( C x. A ) <_ B <-> A <_ ( B / C ) ) )

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
    cle
    wbr
    cC
    cA
    cmul
    co
    #
    cB
    cle
    wbr
    cA
    cB
    cC
    cdiv
    co
    cle
    wbr
    @5
    @6
    @7
    cB
    cle
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
    lemuldiv
    bitr3d
end
