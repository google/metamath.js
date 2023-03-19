include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "wb.mm"
include "simpl.mm"
include "rpregt0.mm"
include "adantl.mm"
include "1re.mm"
include "0lt1.mm"
include "pm3.2i.mm"
include "a1i.mm"
include "ltdiv23.mm"
include "syl3anc.mm"
include "wceq.mm"
include "recn.mm"
include "div1d.mm"
include "adantr.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem divlt1lt
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR+ ) -> ( ( A / B ) < 1 <-> A < B ) )

  proof
    cA
    cr
    wcel
    #
    cB
    crp
    wcel
    #
    wa
    #
    cA
    cB
    cdiv
    co
    c1
    clt
    wbr
    #
    cA
    c1
    cdiv
    co
    #
    cB
    clt
    wbr
    #
    cA
    cB
    clt
    wbr
    @2
    @0
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    wa
    #
    c1
    cr
    wcel
    #
    cc0
    c1
    clt
    wbr
    #
    wa
    #
    @3
    @5
    wb
    @0
    @1
    simpl
    @1
    @6
    @0
    cB
    rpregt0
    adantl
    @9
    @2
    @7
    @8
    1re
    0lt1
    pm3.2i
    a1i
    cA
    cB
    c1
    ltdiv23
    syl3anc
    @2
    @4
    cA
    cB
    clt
    @0
    @4
    cA
    wceq
    @1
    @0
    cA
    cA
    recn
    div1d
    adantr
    breq1d
    bitrd
end
