include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "lemul1a.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "adantrr.mm"
include "3adant2.mm"
include "adantr.mm"
include "3adant1.mm"
include "3brtr3d.mm"

theorem lemul2a
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 <_ C ) ) /\ A <_ B ) -> ( C x. A ) <_ ( C x. B ) )

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
    cle
    wbr
    #
    wa
    #
    w3a
    #
    cA
    cB
    cle
    wbr
    #
    wa
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
    cC
    cA
    cmul
    co
    #
    cC
    cB
    cmul
    co
    #
    cle
    cA
    cB
    cC
    lemul1a
    @5
    @7
    @9
    wceq
    #
    @6
    @0
    @4
    @11
    @1
    @0
    @2
    @11
    @3
    @0
    cA
    cc
    wcel
    cC
    cc
    wcel
    #
    @11
    @2
    cA
    recn
    cC
    recn
    #
    cA
    cC
    mulcom
    syl2an
    adantrr
    3adant2
    adantr
    @5
    @8
    @10
    wceq
    #
    @6
    @1
    @4
    @14
    @0
    @1
    @2
    @14
    @3
    @1
    cB
    cc
    wcel
    @12
    @14
    @2
    cB
    recn
    @13
    cB
    cC
    mulcom
    syl2an
    adantrr
    3adant1
    adantr
    3brtr3d
end
