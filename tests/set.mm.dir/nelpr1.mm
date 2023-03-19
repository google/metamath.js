include "wceq.mm"
include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "animorrl.mm"
include "wb.mm"
include "elprg.mm"
include "syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "mtand.mm"
include "neqned.mm"

theorem nelpr1
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume nelpr1.a: |- ( ph -> A e. V )
  assume nelpr1.n: |- ( ph -> -. A e. { B , C } )


  assert |- ( ph -> A =/= B )

  proof
    wph
    cA
    cB
    wph
    cA
    cB
    wceq
    #
    cA
    cB
    cC
    cpr
    wcel
    #
    nelpr1.n
    wph
    @0
    wa
    @1
    @0
    cA
    cC
    wceq
    #
    wo
    #
    wph
    @0
    @2
    animorrl
    wph
    @1
    @3
    wb
    #
    @0
    wph
    cA
    cV
    wcel
    @4
    nelpr1.a
    cA
    cB
    cC
    cV
    elprg
    syl
    adantr
    mpbird
    mtand
    neqned
end
