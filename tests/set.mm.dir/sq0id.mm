include "cc0.mm"
include "wceq.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "sq0i.mm"
include "syl.mm"

theorem sq0id
  let wph: wff ph
  let cA: class A
  assume sq0id.1: |- ( ph -> A = 0 )


  assert |- ( ph -> ( A ^ 2 ) = 0 )

  proof
    wph
    cA
    cc0
    wceq
    cA
    c2
    cexp
    co
    cc0
    wceq
    sq0id.1
    cA
    sq0i
    syl
end
