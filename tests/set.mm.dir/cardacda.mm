include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "coa.mm"
include "co.mm"
include "ccda.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "cardon.mm"
include "onacda.mm"
include "mp2an.mm"
include "cardid2.mm"
include "cdaen.mm"
include "syl2an.mm"
include "entr.mm"
include "sylancr.mm"
include "ensymd.mm"

theorem cardacda
  let cA: class A
  let cB: class B


  assert |- ( ( A e. dom card /\ B e. dom card ) -> ( A +c B ) ~~ ( ( card ` A ) +o ( card ` B ) ) )

  proof
    cA
    ccrd
    cdm
    #
    wcel
    #
    cB
    @0
    wcel
    #
    wa
    #
    cA
    ccrd
    cfv
    #
    cB
    ccrd
    cfv
    #
    coa
    co
    #
    cA
    cB
    ccda
    co
    #
    @3
    @6
    @4
    @5
    ccda
    co
    #
    cen
    wbr
    #
    @8
    @7
    cen
    wbr
    #
    @6
    @7
    cen
    wbr
    @4
    con0
    wcel
    @5
    con0
    wcel
    @9
    cA
    cardon
    cB
    cardon
    @4
    @5
    onacda
    mp2an
    @1
    @4
    cA
    cen
    wbr
    @5
    cB
    cen
    wbr
    @10
    @2
    cA
    cardid2
    cB
    cardid2
    @4
    cA
    @5
    cB
    cdaen
    syl2an
    @6
    @8
    @7
    entr
    sylancr
    ensymd
end
