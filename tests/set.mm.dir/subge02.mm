include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "cmin.mm"
include "addge01.mm"
include "wb.mm"
include "lesubadd.mm"
include "3anidm13.mm"
include "bitr4d.mm"

theorem subge02
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( 0 <_ B <-> ( A - B ) <_ A ) )

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
    cc0
    cB
    cle
    wbr
    cA
    cA
    cB
    caddc
    co
    cle
    wbr
    #
    cA
    cB
    cmin
    co
    cA
    cle
    wbr
    #
    cA
    cB
    addge01
    @0
    @1
    @3
    @2
    wb
    cA
    cB
    cA
    lesubadd
    3anidm13
    bitr4d
end
