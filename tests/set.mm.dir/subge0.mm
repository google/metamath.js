include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "caddc.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "cmin.mm"
include "wb.mm"
include "0red.mm"
include "simpr.mm"
include "simpl.mm"
include "leaddsub.mm"
include "syl3anc.mm"
include "recnd.mm"
include "addid2d.mm"
include "breq1d.mm"
include "bitr3d.mm"

theorem subge0
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( 0 <_ ( A - B ) <-> B <_ A ) )

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
    cB
    caddc
    co
    #
    cA
    cle
    wbr
    #
    cc0
    cA
    cB
    cmin
    co
    cle
    wbr
    #
    cB
    cA
    cle
    wbr
    @2
    cc0
    cr
    wcel
    @1
    @0
    @4
    @5
    wb
    @2
    0red
    @0
    @1
    simpr
    #
    @0
    @1
    simpl
    cc0
    cB
    cA
    leaddsub
    syl3anc
    @2
    @3
    cB
    cA
    cle
    @2
    cB
    @2
    cB
    @6
    recnd
    addid2d
    breq1d
    bitr3d
end
