include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wf1o.mm"
include "cab.mm"
include "cvv.mm"
include "wf.mm"
include "wss.mm"
include "f1of.mm"
include "anim1i.mm"
include "ss2abi.mm"
include "eqid.mm"
include "fabexg.mm"
include "ssexg.mm"
include "sylancr.mm"
include "syl5eqel.mm"

theorem f1oabexg
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vf: setvar f
  let cF: class F
  assume f1oabexg.1: |- F = { f | ( f : A -1-1-onto-> B /\ ph ) }

  disjoint A f
  disjoint B f
  assert |- ( ( A e. C /\ B e. D ) -> F e. _V )

  proof
    cA
    cC
    wcel
    cB
    cD
    wcel
    wa
    #
    cF
    cA
    cB
    vf
    cv
    #
    wf1o
    #
    wph
    wa
    #
    vf
    cab
    #
    cvv
    f1oabexg.1
    @0
    @4
    cA
    cB
    @1
    wf
    #
    wph
    wa
    #
    vf
    cab
    #
    wss
    @7
    cvv
    wcel
    @4
    cvv
    wcel
    @3
    @6
    vf
    @2
    @5
    wph
    cA
    cB
    @1
    f1of
    anim1i
    ss2abi
    wph
    vf
    cA
    cB
    cC
    cD
    @7
    @7
    eqid
    fabexg
    @4
    @7
    cvv
    ssexg
    sylancr
    syl5eqel
end
