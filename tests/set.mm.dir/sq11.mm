include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "wceq.mm"
include "cmul.mm"
include "cc.mm"
include "simpl.mm"
include "recnd.mm"
include "sqval.mm"
include "syl.mm"
include "eqeqan12d.mm"
include "msq11.mm"
include "bitrd.mm"

theorem sq11
  let cA: class A
  let cB: class B


  assert |- ( ( ( A e. RR /\ 0 <_ A ) /\ ( B e. RR /\ 0 <_ B ) ) -> ( ( A ^ 2 ) = ( B ^ 2 ) <-> A = B ) )

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
    #
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
    #
    wa
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
    wceq
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
    wceq
    cA
    cB
    wceq
    @2
    @5
    @6
    @8
    @7
    @9
    @2
    cA
    cc
    wcel
    @6
    @8
    wceq
    @2
    cA
    @0
    @1
    simpl
    recnd
    cA
    sqval
    syl
    @5
    cB
    cc
    wcel
    @7
    @9
    wceq
    @5
    cB
    @3
    @4
    simpl
    recnd
    cB
    sqval
    syl
    eqeqan12d
    cA
    cB
    msq11
    bitrd
end
