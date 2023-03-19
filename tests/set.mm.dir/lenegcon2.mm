include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "cle.mm"
include "wbr.mm"
include "wb.mm"
include "renegcl.mm"
include "leneg.mm"
include "sylan2.mm"
include "wceq.mm"
include "recn.mm"
include "negnegd.mm"
include "adantl.mm"
include "breq1d.mm"
include "bitrd.mm"

theorem lenegcon2
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <_ -u B <-> B <_ -u A ) )

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
    cneg
    #
    cle
    wbr
    #
    @3
    cneg
    #
    cA
    cneg
    #
    cle
    wbr
    #
    cB
    @6
    cle
    wbr
    @1
    @0
    @3
    cr
    wcel
    @4
    @7
    wb
    cB
    renegcl
    cA
    @3
    leneg
    sylan2
    @2
    @5
    cB
    @6
    cle
    @1
    @5
    cB
    wceq
    @0
    @1
    cB
    cB
    recn
    negnegd
    adantl
    breq1d
    bitrd
end
