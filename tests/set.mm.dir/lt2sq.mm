include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "clt.mm"
include "cmul.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "lt2msq.mm"
include "wb.mm"
include "cc.mm"
include "recn.mm"
include "sqval.mm"
include "breqan12d.mm"
include "syl2an.mm"
include "ad2ant2r.mm"
include "bitr4d.mm"

theorem lt2sq
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( A < B <-> ( A ^ 2 ) < ( B ^ 2 ) ) )

  proof
    cA
    cr
    wcel
    #
    cc0
    cA
    cle
    wbr
    #
    wa
    cB
    cr
    wcel
    #
    cc0
    cB
    cle
    wbr
    #
    wa
    wa
    cA
    cB
    clt
    wbr
    cA
    cA
    cmul
    co
    #
    cB
    cB
    cmul
    co
    #
    clt
    wbr
    #
    cA
    c2
    cexp
    co
    #
    cB
    c2
    cexp
    co
    #
    clt
    wbr
    #
    cA
    cB
    lt2msq
    @0
    @2
    @9
    @6
    wb
    #
    @1
    @3
    @0
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    @10
    @2
    cA
    recn
    cB
    recn
    @11
    @12
    @7
    @4
    @8
    @5
    clt
    cA
    sqval
    cB
    sqval
    breqan12d
    syl2an
    ad2ant2r
    bitr4d
end
