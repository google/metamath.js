include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "wo.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "letric.mm"
include "orcomd.mm"
include "wb.mm"
include "avgle2.mm"
include "ancoms.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "addcom.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "bitr4d.mm"
include "orbi12d.mm"
include "mpbid.mm"

theorem avgle
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( ( ( A + B ) / 2 ) <_ A \/ ( ( A + B ) / 2 ) <_ B ) )

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
    cB
    cA
    cle
    wbr
    #
    cA
    cB
    cle
    wbr
    #
    wo
    cA
    cB
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cA
    cle
    wbr
    #
    @6
    cB
    cle
    wbr
    #
    wo
    @2
    @4
    @3
    cA
    cB
    letric
    orcomd
    @2
    @3
    @7
    @4
    @8
    @2
    @3
    cB
    cA
    caddc
    co
    #
    c2
    cdiv
    co
    #
    cA
    cle
    wbr
    #
    @7
    @1
    @0
    @3
    @11
    wb
    cB
    cA
    avgle2
    ancoms
    @2
    @6
    @10
    cA
    cle
    @2
    @5
    @9
    c2
    cdiv
    @0
    cA
    cc
    wcel
    cB
    cc
    wcel
    @5
    @9
    wceq
    @1
    cA
    recn
    cB
    recn
    cA
    cB
    addcom
    syl2an
    oveq1d
    breq1d
    bitr4d
    cA
    cB
    avgle2
    orbi12d
    mpbid
end
