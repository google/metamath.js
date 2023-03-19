include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "cmul.mm"
include "co.mm"
include "lemulge11.mm"
include "wb.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "breq2d.mm"
include "adantr.mm"
include "mpbid.mm"

theorem lemulge12
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ B e. RR ) /\ ( 0 <_ A /\ 1 <_ B ) ) -> A <_ ( B x. A ) )

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
    c1
    cB
    cle
    wbr
    wa
    #
    wa
    cA
    cA
    cB
    cmul
    co
    #
    cle
    wbr
    #
    cA
    cB
    cA
    cmul
    co
    #
    cle
    wbr
    #
    cA
    cB
    lemulge11
    @2
    @5
    @7
    wb
    @3
    @2
    @4
    @6
    cA
    cle
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @4
    @6
    wceq
    @1
    cA
    recn
    cB
    recn
    cA
    cB
    mulcom
    syl2an
    breq2d
    adantr
    mpbid
end
