include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cle.mm"
include "cmul.mm"
include "co.mm"
include "lemul1.mm"
include "wb.mm"
include "wceq.mm"
include "cc.mm"
include "recn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "3adant2.mm"
include "3adant1.mm"
include "breq12d.mm"
include "3adant3r.mm"
include "bitrd.mm"

theorem lemul2
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( A <_ B <-> ( C x. A ) <_ ( C x. B ) ) )

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
    w3a
    cA
    cB
    cle
    wbr
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
    cle
    wbr
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
    wbr
    #
    cA
    cB
    cC
    lemul1
    @0
    @1
    @2
    @6
    @9
    wb
    @3
    @0
    @1
    @2
    w3a
    @4
    @7
    @5
    @8
    cle
    @0
    @2
    @4
    @7
    wceq
    #
    @1
    @0
    cA
    cc
    wcel
    cC
    cc
    wcel
    #
    @10
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
    3adant2
    @1
    @2
    @5
    @8
    wceq
    #
    @0
    @1
    cB
    cc
    wcel
    @11
    @13
    @2
    cB
    recn
    @12
    cB
    cC
    mulcom
    syl2an
    3adant1
    breq12d
    3adant3r
    bitrd
end
