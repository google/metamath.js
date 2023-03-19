include "wceq.mm"
include "csup.mm"
include "supeq1.mm"
include "syl.mm"

theorem supeq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cR: class R
  assume supeq1d.1: |- ( ph -> B = C )


  assert |- ( ph -> sup ( B , A , R ) = sup ( C , A , R ) )

  proof
    wph
    cB
    cC
    wceq
    cB
    cA
    cR
    csup
    cC
    cA
    cR
    csup
    wceq
    supeq1d.1
    cA
    cB
    cC
    cR
    supeq1
    syl
end
