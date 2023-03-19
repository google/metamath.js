include "wceq.mm"
include "cpw.mm"
include "pweq.mm"
include "syl.mm"

theorem pweqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume pweqd.1: |- ( ph -> A = B )


  assert |- ( ph -> ~P A = ~P B )

  proof
    wph
    cA
    cB
    wceq
    cA
    cpw
    cB
    cpw
    wceq
    pweqd.1
    cA
    cB
    pweq
    syl
end
