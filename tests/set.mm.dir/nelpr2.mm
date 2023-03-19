include "wceq.mm"
include "cpr.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "animorr.mm"
include "wb.mm"
include "elprg.mm"
include "syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "mtand.mm"
include "neqned.mm"

theorem nelpr2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume nelpr2.a: |- ( ph -> A e. V )
  assume nelpr2.n: |- ( ph -> -. A e. { B , C } )


  assert |- ( ph -> A =/= C )

  proof
    wph
    cA
    cC
    wph
    cA
    cC
    wceq
    #
    cA
    cB
    cC
    cpr
    wcel
    #
    nelpr2.n
    wph
    @0
    wa
    @1
    cA
    cB
    wceq
    #
    @0
    wo
    #
    wph
    @0
    @2
    animorr
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
    nelpr2.a
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
