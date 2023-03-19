include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "cc0.mm"
include "wb.mm"
include "leaddsub2.mm"
include "3anidm13.mm"
include "wceq.mm"
include "recn.mm"
include "subidd.mm"
include "adantr.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem leaddle0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( A + B ) <_ A <-> B <_ 0 ) )

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
    cA
    cB
    caddc
    co
    cA
    cle
    wbr
    #
    cB
    cA
    cA
    cmin
    co
    #
    cle
    wbr
    #
    cB
    cc0
    cle
    wbr
    @0
    @1
    @3
    @5
    wb
    cA
    cB
    cA
    leaddsub2
    3anidm13
    @2
    @4
    cc0
    cB
    cle
    @0
    @4
    cc0
    wceq
    @1
    @0
    cA
    cA
    recn
    subidd
    adantr
    breq2d
    bitrd
end
