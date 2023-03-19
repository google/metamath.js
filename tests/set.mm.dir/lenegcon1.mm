include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "renegcl.mm"
include "leneg.mm"
include "sylan.mm"
include "recn.mm"
include "negnegd.mm"
include "breq2d.mm"
include "adantr.mm"
include "bitrd.mm"

theorem lenegcon1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( -u A <_ B <-> -u B <_ A ) )

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
    cA
    cneg
    #
    cB
    cle
    wbr
    #
    cB
    cneg
    #
    @2
    cneg
    #
    cle
    wbr
    #
    @4
    cA
    cle
    wbr
    #
    @0
    @2
    cr
    wcel
    @1
    @3
    @6
    wb
    cA
    renegcl
    @2
    cB
    leneg
    sylan
    @0
    @6
    @7
    wb
    @1
    @0
    @5
    cA
    @4
    cle
    @0
    cA
    cA
    recn
    negnegd
    breq2d
    adantr
    bitrd
end
