include "wne.mm"
include "wceq.mm"
include "adantl.mm"
include "pm2.61dane.mm"
include "pm2.61ine.mm"

theorem pm2.61iine
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume pm2.61iine.1: |- ( ( A =/= C /\ B =/= D ) -> ph )
  assume pm2.61iine.2: |- ( A = C -> ph )
  assume pm2.61iine.3: |- ( B = D -> ph )


  assert |- ph

  proof
    wph
    cA
    cC
    pm2.61iine.2
    cA
    cC
    wne
    #
    wph
    cB
    cD
    cB
    cD
    wceq
    wph
    @0
    pm2.61iine.3
    adantl
    pm2.61iine.1
    pm2.61dane
    pm2.61ine
end
