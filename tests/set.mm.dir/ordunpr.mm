include "con0.mm"
include "wcel.mm"
include "wa.mm"
include "cun.mm"
include "cpr.mm"
include "wceq.mm"
include "wo.mm"
include "wss.mm"
include "word.mm"
include "eloni.mm"
include "ordtri2or2.mm"
include "syl2an.mm"
include "orcomd.mm"
include "ssequn2.mm"
include "ssequn1.mm"
include "orbi12i.mm"
include "sylib.mm"
include "cvv.mm"
include "wb.mm"
include "unexg.mm"
include "elprg.mm"
include "syl.mm"
include "mpbird.mm"

theorem ordunpr
  let cB: class B
  let cC: class C


  assert |- ( ( B e. On /\ C e. On ) -> ( B u. C ) e. { B , C } )

  proof
    cB
    con0
    wcel
    #
    cC
    con0
    wcel
    #
    wa
    #
    cB
    cC
    cun
    #
    cB
    cC
    cpr
    wcel
    #
    @3
    cB
    wceq
    #
    @3
    cC
    wceq
    #
    wo
    #
    @2
    cC
    cB
    wss
    #
    cB
    cC
    wss
    #
    wo
    @7
    @2
    @9
    @8
    @0
    cB
    word
    cC
    word
    @9
    @8
    wo
    @1
    cB
    eloni
    cC
    eloni
    cB
    cC
    ordtri2or2
    syl2an
    orcomd
    @8
    @5
    @9
    @6
    cC
    cB
    ssequn2
    cB
    cC
    ssequn1
    orbi12i
    sylib
    @2
    @3
    cvv
    wcel
    @4
    @7
    wb
    cB
    cC
    con0
    con0
    unexg
    @3
    cB
    cC
    cvv
    elprg
    syl
    mpbird
end
