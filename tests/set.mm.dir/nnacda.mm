include "com.mm"
include "wcel.mm"
include "wa.mm"
include "coa.mm"
include "co.mm"
include "ccrd.mm"
include "cfv.mm"
include "ccda.mm"
include "cen.mm"
include "wbr.mm"
include "wceq.mm"
include "con0.mm"
include "nnon.mm"
include "onacda.mm"
include "syl2an.mm"
include "carden2b.mm"
include "syl.mm"
include "nnacl.mm"
include "cardnn.mm"
include "eqtr3d.mm"

theorem nnacda
  let cA: class A
  let cB: class B


  assert |- ( ( A e. _om /\ B e. _om ) -> ( card ` ( A +c B ) ) = ( A +o B ) )

  proof
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    wa
    #
    cA
    cB
    coa
    co
    #
    ccrd
    cfv
    #
    cA
    cB
    ccda
    co
    #
    ccrd
    cfv
    #
    @3
    @2
    @3
    @5
    cen
    wbr
    #
    @4
    @6
    wceq
    @0
    cA
    con0
    wcel
    cB
    con0
    wcel
    @7
    @1
    cA
    nnon
    cB
    nnon
    cA
    cB
    onacda
    syl2an
    @3
    @5
    carden2b
    syl
    @2
    @3
    com
    wcel
    @4
    @3
    wceq
    cA
    cB
    nnacl
    @3
    cardnn
    syl
    eqtr3d
end
