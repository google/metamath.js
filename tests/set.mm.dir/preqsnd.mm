include "cvv.mm"
include "wcel.mm"
include "cpr.mm"
include "csn.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "dfsn2.mm"
include "eqeq2i.mm"
include "wo.mm"
include "preq12bg.mm"
include "oridm.mm"
include "syl6bb.mm"
include "syl5bb.mm"
include "syl22anc.mm"

theorem preqsnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume preqsnd.1: |- ( ph -> A e. _V )
  assume preqsnd.2: |- ( ph -> B e. _V )
  assume preqsnd.3: |- ( ph -> C e. _V )


  assert |- ( ph -> ( { A , B } = { C } <-> ( A = C /\ B = C ) ) )

  proof
    wph
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    cC
    cvv
    wcel
    #
    @2
    cA
    cB
    cpr
    #
    cC
    csn
    #
    wceq
    #
    cA
    cC
    wceq
    cB
    cC
    wceq
    wa
    #
    wb
    preqsnd.1
    preqsnd.2
    preqsnd.3
    preqsnd.3
    @5
    @3
    cC
    cC
    cpr
    #
    wceq
    #
    @0
    @1
    wa
    @2
    @2
    wa
    wa
    #
    @6
    @4
    @7
    @3
    cC
    dfsn2
    eqeq2i
    @9
    @8
    @6
    @6
    wo
    @6
    cA
    cB
    cC
    cC
    cvv
    cvv
    cvv
    cvv
    preq12bg
    @6
    oridm
    syl6bb
    syl5bb
    syl22anc
end
