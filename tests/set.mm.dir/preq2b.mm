include "cpr.mm"
include "wceq.mm"
include "prcom.mm"
include "eqeq12i.mm"
include "preq1b.mm"
include "syl5bb.mm"

theorem preq2b
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  let cW: class W
  assume preq1b.a: |- ( ph -> A e. V )
  assume preq1b.b: |- ( ph -> B e. W )


  assert |- ( ph -> ( { C , A } = { C , B } <-> A = B ) )

  proof
    cC
    cA
    cpr
    #
    cC
    cB
    cpr
    #
    wceq
    cA
    cC
    cpr
    #
    cB
    cC
    cpr
    #
    wceq
    wph
    cA
    cB
    wceq
    @0
    @2
    @1
    @3
    cC
    cA
    prcom
    cC
    cB
    prcom
    eqeq12i
    wph
    cA
    cB
    cC
    cV
    cW
    preq1b.a
    preq1b.b
    preq1b
    syl5bb
end
