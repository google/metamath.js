include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cneg.mm"
include "clt.mm"
include "wbr.mm"
include "wb.mm"
include "renegcl.mm"
include "ltneg.mm"
include "sylan.mm"
include "simpl.mm"
include "recnd.mm"
include "negnegd.mm"
include "breq2d.mm"
include "bitrd.mm"

theorem ltnegcon1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( -u A < B <-> -u B < A ) )

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
    cneg
    #
    cB
    clt
    wbr
    #
    cB
    cneg
    #
    @3
    cneg
    #
    clt
    wbr
    #
    @5
    cA
    clt
    wbr
    @0
    @3
    cr
    wcel
    @1
    @4
    @7
    wb
    cA
    renegcl
    @3
    cB
    ltneg
    sylan
    @2
    @6
    cA
    @5
    clt
    @2
    cA
    @2
    cA
    @0
    @1
    simpl
    recnd
    negnegd
    breq2d
    bitrd
end
