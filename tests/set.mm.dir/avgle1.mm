include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "caddc.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wb.mm"
include "avglt2.mm"
include "ancoms.mm"
include "cc.mm"
include "wceq.mm"
include "recn.mm"
include "addcom.mm"
include "syl2an.mm"
include "oveq1d.mm"
include "breq1d.mm"
include "bitr4d.mm"
include "notbid.mm"
include "lenlt.mm"
include "readdcl.mm"
include "rehalfcl.mm"
include "syl.mm"
include "syldan.mm"
include "3bitr4d.mm"

theorem avgle1
  let cA: class A
  let cB: class B


  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <_ B <-> A <_ ( ( A + B ) / 2 ) ) )

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
    clt
    wbr
    #
    wn
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
    clt
    wbr
    #
    wn
    #
    cA
    cB
    cle
    wbr
    cA
    @5
    cle
    wbr
    #
    @2
    @3
    @6
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
    clt
    wbr
    #
    @6
    @1
    @0
    @3
    @11
    wb
    cB
    cA
    avglt2
    ancoms
    @2
    @5
    @10
    cA
    clt
    @2
    @4
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
    @4
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
    notbid
    cA
    cB
    lenlt
    @0
    @1
    @5
    cr
    wcel
    #
    @8
    @7
    wb
    @2
    @4
    cr
    wcel
    @12
    cA
    cB
    readdcl
    @4
    rehalfcl
    syl
    cA
    @5
    lenlt
    syldan
    3bitr4d
end
