include "wceq.mm"
include "eqeq2d.mm"
include "mpbid.mm"

theorem eqtrd
  param wph: wff ph
  param cA: class A
  param cB: class B
  param cC: class C
  assume eqtrd.1: |- ( ph -> A = B )
  assume eqtrd.2: |- ( ph -> B = C )


  assert |- ( ph -> A = C )

  proof
    wph
    cA
    cB
    wceq
    cA
    cC
    wceq
    eqtrd.1
    wph
    cB
    cC
    cA
    eqtrd.2
    eqeq2d
    mpbid
end
