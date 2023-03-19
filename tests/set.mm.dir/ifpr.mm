include "wcel.mm"
include "cvv.mm"
include "cif.mm"
include "cpr.mm"
include "elex.mm"
include "wa.mm"
include "ifcl.mm"
include "wceq.mm"
include "wo.mm"
include "ifeqor.mm"
include "elprg.mm"
include "mpbiri.mm"
include "syl.mm"
include "syl2an.mm"

theorem ifpr
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( A e. C /\ B e. D ) -> if ( ph , A , B ) e. { A , B } )

  proof
    cA
    cC
    wcel
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wph
    cA
    cB
    cif
    #
    cA
    cB
    cpr
    wcel
    #
    cB
    cD
    wcel
    cA
    cC
    elex
    cB
    cD
    elex
    @0
    @1
    wa
    @2
    cvv
    wcel
    #
    @3
    wph
    cA
    cB
    cvv
    ifcl
    @4
    @3
    @2
    cA
    wceq
    @2
    cB
    wceq
    wo
    wph
    cA
    cB
    ifeqor
    @2
    cA
    cB
    cvv
    elprg
    mpbiri
    syl
    syl2an
end
