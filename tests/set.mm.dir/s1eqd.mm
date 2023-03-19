include "wceq.mm"
include "cs1.mm"
include "s1eq.mm"
include "syl.mm"

theorem s1eqd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume s1eqd.1: |- ( ph -> A = B )


  assert |- ( ph -> <" A "> = <" B "> )

  proof
    wph
    cA
    cB
    wceq
    cA
    cs1
    cB
    cs1
    wceq
    s1eqd.1
    cA
    cB
    s1eq
    syl
end
