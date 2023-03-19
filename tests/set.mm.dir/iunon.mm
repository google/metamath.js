include "wcel.mm"
include "con0.mm"
include "wral.mm"
include "wa.mm"
include "ciun.mm"
include "cmpt.mm"
include "crn.mm"
include "cuni.mm"
include "wceq.mm"
include "dfiun3g.mm"
include "adantl.mm"
include "cvv.mm"
include "wss.mm"
include "mptexg.mm"
include "rnexg.mm"
include "syl.mm"
include "eqid.mm"
include "rnmptss.mm"
include "ssonuni.mm"
include "imp.mm"
include "syl2an.mm"
include "eqeltrd.mm"

theorem iunon
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cV: class V

  disjoint A x
  assert |- ( ( A e. V /\ A. x e. A B e. On ) -> U_ x e. A B e. On )

  proof
    cA
    cV
    wcel
    #
    cB
    con0
    wcel
    vx
    cA
    wral
    #
    wa
    vx
    cA
    cB
    ciun
    #
    vx
    cA
    cB
    cmpt
    #
    crn
    #
    cuni
    #
    con0
    @1
    @2
    @5
    wceq
    @0
    vx
    cA
    cB
    con0
    dfiun3g
    adantl
    @0
    @4
    cvv
    wcel
    #
    @4
    con0
    wss
    #
    @5
    con0
    wcel
    #
    @1
    @0
    @3
    cvv
    wcel
    @6
    vx
    cA
    cB
    cV
    mptexg
    @3
    cvv
    rnexg
    syl
    vx
    cA
    cB
    con0
    @3
    @3
    eqid
    rnmptss
    @6
    @7
    @8
    @4
    cvv
    ssonuni
    imp
    syl2an
    eqeltrd
end
